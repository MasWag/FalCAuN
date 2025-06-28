package net.maswag.falcaun;

import de.learnlib.exception.SULException;
import de.learnlib.sul.SUL;
import jep.JepException;
import lombok.Getter;
import net.automatalib.word.Word;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import java.io.Closeable;
import java.util.List;
import java.util.ArrayList;
import java.util.concurrent.ExecutionException;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class PythonNumericSUL implements NumericSUL, Closeable {
    /**
     * Use rawtypes because classobject does not support generic type
     */
    @SuppressWarnings("rawtypes")
    protected final PythonModel<List<Double>, ArrayList> model;

    @Getter
    private int counter = 0;

    /**
     * @param initScript The Python script to initialize the model. It defines a
     *                   class SUL with methods pre(), post(), step(I inputSignal)
     *                   -> O, and close().
     * @throws JepException If there is an error initializing the Python interpreter
     *                      or running the script.
     */
    @SuppressWarnings("rawtypes")
    public PythonNumericSUL(String initScript)
            throws JepException {
        this.model = new PythonModel<List<Double>, ArrayList>(initScript, ArrayList.class);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean canFork() {
        return false;
    }

    /**
     * Clear the counter and the time measure.
     */
    @Override
    public void clear() {
        this.model.getSimulationTime().reset();
        counter = 0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void pre() {
        this.model.pre();
        counter++;
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
    public IOSignalPiece<List<Double>> step(@Nullable List<Double> inputSignal)
            throws SULException {
        if (inputSignal == null) {
            return null;
        }

        List<?> ret;
        try {
            ret = this.model.step(inputSignal);
        } catch (JepException e) {
            throw new SULException(e);
        }
        Stream<?> stream = ret.stream();
        var outputSignal = stream.map(e -> Double.class.cast(e)).collect(Collectors.toList());
        return new IOSignalPiece<>(inputSignal, outputSignal);
    }

    /**
     * Run all steps of the python model by feeding inputSignal
     *
     * @param inputSignal The input signal
     * @return The output signal. The size is same as the input.
     */
    @Override
    public IOSignal<List<Double>> execute(Word<List<Double>> inputSignal)
            throws InterruptedException, ExecutionException {
        pre();

        ArrayList<List<Double>> outputs = new ArrayList<List<Double>>();
        ArrayList<?> ret;

        for (var e : inputSignal) {
            try {
                ret = this.model.step(e);
            } catch (JepException exc) {
                throw new ExecutionException(exc);
            }

            Stream<?> stream = ret.stream();
            var output = stream.map(obj -> Double.class.cast(obj)).collect(Collectors.toList());
            outputs.add(output);
        }
        var outputSignal = Word.fromList(outputs);
        return new IODiscreteSignal<>(inputSignal, outputSignal);
    }

    /**
     * {@inheritDoc}
     */
    @Nonnull
    @Override
    public SUL<List<Double>, IOSignalPiece<List<Double>>> fork() throws UnsupportedOperationException {
        throw new UnsupportedOperationException();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void close() {
        this.model.close();
    }

    /**
     * {@inheritDoc}
     */
    public double getSimulationTimeSecond() {
        return this.model.getSimulationTime().getSecond();
    }
}
