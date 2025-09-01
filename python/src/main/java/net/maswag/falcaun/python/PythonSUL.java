package net.maswag.falcaun.python;

import de.learnlib.exception.SULException;
import de.learnlib.sul.SUL;
import jep.JepException;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import java.io.Closeable;

/**
 * The System Under Learning implemented by a Python model.
 */
public class PythonSUL<I, O> implements SUL<I, O>, Closeable {
    protected final PythonModel<I, O> model;

    /**
     * @param initScript The Python script to initialize the model.
     *                   It defines a class SUL with methods pre(), post(), step(I inputSignal) -> O, and close().
     * @param outputClass The class object of the output signal produced by the step method.
     */
    public PythonSUL(String initScript, Class<O> outputClass) throws JepException {
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
    public O step(@Nullable I inputSignal)
            throws SULException {
        if (inputSignal == null) {
            return null;
        }

        try {
            return this.model.step(inputSignal);
        } catch (JepException e) {
            throw new SULException(e);
        }
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
