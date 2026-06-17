package net.maswag.falcaun.simulink;

import com.mathworks.engine.EngineException;
import com.mathworks.engine.MatlabEngine;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.io.Closeable;
import java.io.IOException;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.channels.OverlappingFileLockException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ThreadLocalRandom;

/**
 * Manages safe MATLAB engine lifecycle: discovery of reusable FalCAuN-owned
 * sessions protected by inter-process file locks, and creation of new named
 * shared engines when no safe session exists.
 *
 * Engine reuse is controlled by the system property
 * {@code falcaun.matlab.reuseEngine} (default {@code true}).
 */
final class MatlabEngineManager {
    private static final Logger log = LoggerFactory.getLogger(MatlabEngineManager.class);

    static final String ENGINE_NAME_PREFIX = "FalCAuN_";
    private static final String LOCK_SUBDIR = "falcaun-matlab-engine-locks";
    private static final Map<String, MatlabEngine> REUSABLE_ENGINES = new ConcurrentHashMap<>();

    static final boolean REUSE_ENGINE = Boolean.parseBoolean(
        System.getProperty("falcaun.matlab.reuseEngine", "true")
    );

    private MatlabEngineManager() {
        // utility class
    }

    // -----------------------------------------------------------------------
    // Public API
    // -----------------------------------------------------------------------

    /**
     * Acquire a safe MATLAB engine: either a FalCAuN-owned reusable session
     * (protected by a file lock) or a freshly started named shared engine.
     */
    static LockedMatlabEngine acquireEngine() throws EngineException {
        // Check system property before doing anything
        if (!REUSE_ENGINE) {
            log.debug("Engine reuse disabled (falcaun.matlab.reuseEngine=false), starting fresh");
            return startNewEngine(false);
        }

        LockedMatlabEngine locked = tryReuseExisting();
        if (locked != null) {
            return locked;
        }

        return startNewEngine(true);
    }

    // -----------------------------------------------------------------------
    // Reuse path
    // -----------------------------------------------------------------------

    private static LockedMatlabEngine tryReuseExisting() {
        String[] engines;
        try {
            engines = MatlabEngine.findMatlab();
        } catch (Exception e) {
            log.debug("Error listing MATLAB sessions: {}", e.getMessage());
            return null;
        }
        if (engines.length == 0) {
            log.debug("No MATLAB engines found for reuse");
            return null;
        }

        for (String name : engines) {
            if (!name.startsWith(ENGINE_NAME_PREFIX)) {
                log.debug("Skipping non-FalCAuN engine: {}", name);
                continue;
            }
            LockedMatlabEngine locked = acquireOneSession(name);
            if (locked != null) {
                return locked;
            }
        }
        log.debug("No FalCAuN-owned session that we can lock was found");
        return null;
    }

    private static LockedMatlabEngine acquireOneSession(String name) {
        Path lockPath = lockFilePath(name);
        FileChannel channel = null;
        FileLock lock = null;
        try {
            // Ensure lock directory exists
            Path lockDir = lockPath.getParent();
            if (lockDir != null && !Files.exists(lockDir)) {
                Files.createDirectories(lockDir);
            }

            channel = FileChannel.open(
                lockPath,
                StandardOpenOption.CREATE,
                StandardOpenOption.WRITE
            );
            lock = channel.tryLock();
            if (lock == null) {
                // Session is locked by another process
                channel.close();
                log.debug("Session '{}' already locked by another process, skipping", name);
                return null;
            }

            // Lock acquired — try to connect
            MatlabEngine eng;
            LockedMatlabEngine.CloseAction closeAction;
            MatlabEngine pooledEngine = REUSABLE_ENGINES.get(name);
            if (pooledEngine != null) {
                eng = pooledEngine;
                closeAction = LockedMatlabEngine.CloseAction.KEEP_ALIVE;
                log.debug("Reusing pooled FalCAuN session: {}", name);
            } else {
                try {
                    eng = MatlabEngine.connectMatlab(name);
                    closeAction = LockedMatlabEngine.CloseAction.DISCONNECT;
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                    log.debug("Interrupted while connecting to session '{}'", name);
                    releaseLockQuietly(lock, channel);
                    return null;
                }
            }
            // Engine handle is usable: keep the lock, return wrapper.
            log.debug("Acquired usable locked FalCAuN session: {}", name);
            return new LockedMatlabEngine(eng, channel, lock, closeAction);
        } catch (IOException | OverlappingFileLockException e) {
            log.debug("Failed to acquire lock for session '{}': {}", name, e.getMessage());
            releaseLockQuietly(lock, channel);
            return null;
        } catch (EngineException e) {
            log.debug("Locked FalCAuN session '{}' was not connectable: {}", name, e.getMessage());
            releaseLockQuietly(lock, channel);
            return null;
        }
    }

    // -----------------------------------------------------------------------
    // New-engine path
    // -----------------------------------------------------------------------

    private static LockedMatlabEngine startNewEngine(boolean reusable) throws EngineException {
        String name = generateUniqueName();
        log.debug("Starting new MATLAB engine, name={}, reusable={}", name, reusable);

        MatlabEngine eng;
        try {
            eng = MatlabEngine.startMatlab();
        } catch (EngineException e) {
            throw new EngineException("Failed to start new MATLAB engine", e);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new EngineException("Interrupted while starting new MATLAB engine", e);
        }

        if (reusable) {
            // Give the engine a name and share it so it can be connected later.
            try {
                // shareEngine('name') is a static method in the matlab.engine package.
                // Variable name must be valid MATLAB variable.
                eng.eval("falcaun_name = '" + name + "';");
                eng.eval("matlab.engine.shareEngine(falcaun_name);");
                eng.eval("clear falcaun_name;");
            } catch (EngineException e) {
                closeEngineQuietly(eng);
                throw new EngineException("Failed to share newly started MATLAB engine: " + e.getMessage(), e);
            } catch (ExecutionException e) {
                closeEngineQuietly(eng);
                throw new EngineException("Failed to share newly started MATLAB engine: " + e.getMessage(), e);
            } catch (InterruptedException e) {
                closeEngineQuietly(eng);
                Thread.currentThread().interrupt();
                throw new EngineException("Interrupted while sharing engine", e);
            } catch (Exception e) {
                closeEngineQuietly(eng);
                throw new EngineException("Failed to share newly started MATLAB engine: " + e.getMessage(), e);
            }
        }

        // Acquire and hold the lock for the newly started engine. We already have
        // the engine handle, so avoid reconnecting to a session we just started.
        LockedMatlabEngine locked = lockAlreadyStartedEngine(name, eng, reusable);
        if (locked == null) {
            closeEngineQuietly(eng);
            throw new EngineException("Could not acquire lock for newly started engine: " + name);
        }
        return locked;
    }

    static LockedMatlabEngine lockAlreadyStartedEngine(String name, MatlabEngine eng, boolean reusable) {
        Path lockPath = lockFilePath(name);
        FileChannel channel = null;
        FileLock lock = null;
        try {
            Path lockDir = lockPath.getParent();
            if (lockDir != null && !Files.exists(lockDir)) {
                Files.createDirectories(lockDir);
            }
            channel = FileChannel.open(
                lockPath,
                StandardOpenOption.CREATE,
                StandardOpenOption.WRITE
            );
            lock = channel.tryLock();
            if (lock == null) {
                channel.close();
                log.debug("Newly started session '{}' is already locked", name);
                return null;
            }
            LockedMatlabEngine.CloseAction closeAction = reusable
                    ? LockedMatlabEngine.CloseAction.KEEP_ALIVE
                    : LockedMatlabEngine.CloseAction.TERMINATE;
            if (reusable) {
                REUSABLE_ENGINES.put(name, eng);
            }
            log.debug("Acquired inter-process lock for newly started FalCAuN engine: {}, reusable={}", name, reusable);
            return new LockedMatlabEngine(eng, channel, lock, closeAction);
        } catch (IOException | OverlappingFileLockException e) {
            log.debug("Failed to lock newly started session '{}': {}", name, e.getMessage());
            releaseLockQuietly(lock, channel);
            return null;
        }
    }

    // -----------------------------------------------------------------------
    // Helper: name generation & validation
    // -----------------------------------------------------------------------

    static String generateUniqueName() {
        long pid = ProcessHandle.current().pid();
        String hex = String.format("%06x", ThreadLocalRandom.current().nextInt(0xFFFFFF));
        return ENGINE_NAME_PREFIX + pid + "_" + hex;
    }

    static boolean isValidMatlabVarName(String name) {
        if (name == null || name.isEmpty()) {
            return false;
        }
        // MATLAB variable names must not start with a digit
        char first = name.charAt(0);
        if (first >= '0' && first <= '9') {
            return false;
        }
        // Only letters, digits, and underscores
        for (int i = 0; i < name.length(); i++) {
            char c = name.charAt(i);
            boolean ok = (c >= 'A' && c <= 'Z') ||
                         (c >= 'a' && c <= 'z') ||
                         (c >= '0' && c <= '9') ||
                         (c == '_') ||
                         (c >= 128); // allow Unicode for safety
            if (!ok) {
                return false;
            }
        }
        return true;
    }

    static String lockFileName(String engineName) {
        // MATLAB engine names are valid variable names (letters, digits, _),
        // so they are safe to use directly in file names
        return engineName + ".lock";
    }

    static Path lockFilePath(String engineName) {
        String tmpDir = System.getProperty("java.io.tmpdir");
        Path lockDir = Path.of(tmpDir, LOCK_SUBDIR);
        return lockDir.resolve(lockFileName(engineName));
    }

    // -----------------------------------------------------------------------
    // Quiet close helpers
    // -----------------------------------------------------------------------

    private static void releaseLockQuietly(FileLock lock, FileChannel channel) {
        if (lock != null && lock.isValid()) {
            try { lock.release(); } catch (IOException ignored) {}
        }
        closeQuietly(channel);
    }

    private static void closeQuietly(Closeable c) {
        if (c != null) {
            try { c.close(); } catch (IOException ignored) {}
        }
    }

    private static void closeEngineQuietly(MatlabEngine e) {
        if (e != null) {
            try { e.close(); } catch (EngineException ignored) {}
        }
    }
}
