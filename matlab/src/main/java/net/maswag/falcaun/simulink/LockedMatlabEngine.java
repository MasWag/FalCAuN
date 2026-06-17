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
 * The lock is released before the engine is closed.
 */
final class LockedMatlabEngine implements AutoCloseable {
    private final MatlabEngine engine;
    private final FileChannel lockChannel;
    private final FileLock lock;

    LockedMatlabEngine(MatlabEngine engine, FileChannel lockChannel, FileLock lock) {
        this.engine = engine;
        this.lockChannel = lockChannel;
        this.lock = lock;
    }

    MatlabEngine engine() {
        return engine;
    }

    @Override
    public void close() throws EngineException {
        try {
            engine.close();
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
