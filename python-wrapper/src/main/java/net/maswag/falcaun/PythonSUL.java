package net.maswag.falcaun;

import de.learnlib.sul.SUL;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import java.io.Closeable;
import java.util.concurrent.ExecutionException;

/**
 * The System Under Learning implemented by a Python model.
 */
public class PythonSUL<I, O> implements SUL<I, O>, Closeable {
    protected final PythonModel<I, O> model;
    protected final TimeMeasure simulationTime = new TimeMeasure();

    /**
     * @param initScript The Python script to initialize the model.
     *                   It defines a class SUL with methods pre(), post(), step(I inputSignal) -> O, and close().
     * @param outputClass The class object of the output signal produced by the step method.
     */
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
     * {@inheritDoc}
     */
    @Override
    public void close() {
        this.model.close();
    }
}
