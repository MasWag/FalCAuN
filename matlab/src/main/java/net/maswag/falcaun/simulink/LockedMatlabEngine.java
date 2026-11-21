package net.maswag.falcaun.simulink;

import com.mathworks.engine.EngineException;
import com.mathworks.engine.MatlabEngine;

import java.io.IOException;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;

/**
 * Wraps a {@link MatlabEngine} with an inter-process {@link FileLock}
 * to ensure safe, exclusive access to a shared MATLAB session.
 *
 * The lock is released after the Java engine handle is released.
 */
final class LockedMatlabEngine implements AutoCloseable {
    enum CloseAction {
        DISCONNECT,
        KEEP_ALIVE,
        TERMINATE
    }

    private final String name;
    private final MatlabEngine engine;
    private final FileChannel lockChannel;
    private final FileLock lock;
    private final CloseAction closeAction;
    private boolean broken = false;

    LockedMatlabEngine(String name, MatlabEngine engine, FileChannel lockChannel, FileLock lock, CloseAction closeAction) {
        this.name = name;
        this.engine = engine;
        this.lockChannel = lockChannel;
        this.lock = lock;
        this.closeAction = closeAction;
    }

    MatlabEngine engine() {
        return engine;
    }

    /**
     * Mark the session as unusable, e.g., after MATLAB crashed while executing a command.
     * A broken session started by this process is terminated on {@link #close()} instead of being kept for reuse.
     */
    void markBroken() {
        broken = true;
    }

    @Override
    public void close() throws EngineException {
        try {
            if (engine == null) {
                return;
            } else if (closeAction == CloseAction.DISCONNECT) {
                engine.disconnect();
            } else if (closeAction == CloseAction.TERMINATE || broken) {
                MatlabEngineManager.terminateEngine(name, engine);
            }
        } finally {
            try {
                if (lock != null && lock.isValid()) {
                    lock.release();
                }
            } catch (IOException e) {
                // ignore lock release errors
            } finally {
                try {
                    if (lockChannel != null && lockChannel.isOpen()) {
                        lockChannel.close();
                    }
                } catch (IOException e) {
                    // ignore lock channel close errors
                }
            }
        }
    }
}
