package net.maswag.falcaun;

import de.learnlib.sul.SUL;
import lombok.extern.slf4j.Slf4j;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import java.io.Closeable;
import java.util.concurrent.ExecutionException;

/**
 * The System Under Learning implemented by a Simulink. We use the fixed step
 * execution of Simulink to make sampling easier.
 */
@Slf4j
public class PythonSUL<I, O> implements SUL<I, O>, Closeable {
    protected final PythonModel<I, O> model;
    protected final TimeMeasure simulationTime = new TimeMeasure();

    public PythonSUL(String initScript, Class<O> outputClass) throws InterruptedException, ExecutionException {
        this.model = new PythonModel<I, O>(initScript, outputClass);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean canFork() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void pre() {
        this.model.pre();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void post() {
        this.model.post();
    }

    /**
     * {@inheritDoc}
     */
    @Nullable
    @Override
    public O step(@Nullable I inputSignal) {
        if (inputSignal == null) {
            return null;
        }

        simulationTime.start();
        O outputSignal = this.model.step(inputSignal);
        simulationTime.stop();

        return outputSignal;
    }

    /**
     * {@inheritDoc}
     */
    @Nonnull
    @Override
    public SUL<I, O> fork() throws UnsupportedOperationException {
        throw new UnsupportedOperationException();
    }

    /**
     * Close the MATLAB engine. This method must be called when the object is no
     * longer used.
     */
    @Override
    public void close() {
        this.model.close();
    }
}
