package net.maswag.falcaun;

import de.learnlib.exception.SULException;
import de.learnlib.sul.SUL;
import jep.JepException;
import lombok.Getter;
import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import java.io.Closeable;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.stream.Collectors;
import java.util.stream.Stream;


public class PythonContinuousNumericSUL implements ContinuousNumericSUL, Closeable {
    /**
     * The signal step of the input signal.
     */
    protected final Double signalStep;

    /**
     * Use rawtypes because classobject does not support generic type
     */
    @SuppressWarnings("rawtypes")
    protected final PythonModel<List<Double>, ArrayList> model;
    protected Signal inputSignal = null;

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
    public PythonContinuousNumericSUL(String initScript, Double signalStep)
            throws JepException {
        this.model = new PythonModel<List<Double>, ArrayList>(initScript, ArrayList.class);
        this.signalStep = signalStep;
    }

    /**
     * The current time of the simulation
     */
    public double getCurrentTime() {
        return inputSignal.duration();
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
        inputSignal = new Signal(signalStep);
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

    private ValueWithTime<List<Double>> constructValueWithTime(@SuppressWarnings("rawtypes") ArrayList<?> ary) {
        // Convert the raw list to a typed list with runtime type checking
        List<List<Double>> data = ary.stream().map(e1 -> {
                Stream<?> s = List.class.cast(e1).stream();
                return s.map(e2 -> Double.class.cast(e2)).collect(Collectors.toList());
            }).collect(Collectors.toList());

        var length1 = data.size();
        if (length1 == 0) {
            throw new IllegalArgumentException("Input data is empty.");
        }
        var length2 = data.get(0).size();
        if (length2 < 2) {
            throw new IllegalArgumentException("Each row must contain at least a timestamp and one output value.");
        }

        var timestamps = new ArrayList<Double>();
        var result = new ArrayList<List<Double>>();
        for (int i = 0; i < length1; i++) {
            timestamps.add(data.get(i).get(0));
            result.add(data.get(i).subList(1, length2));
        }
        return new ValueWithTime<List<Double>>(timestamps, result);
    }

    /**
     * Make one step on the SUL in python.
     * step function in python must return a 2D numpy array
     * which first column is the timestamp and the rest columns are the output values.
     *
     * @param inputSignal The input signal to the SUL
     * @return output of SUL
     *
     * @throws SULException
     *         if the input symbol cannot be executed on the SUL
     */
    @Nullable
    @Override
    public ExtendedIOSignalPiece<List<Double>> step(@Nullable List<Double> inputSignal) 
            throws SULException {
        if (inputSignal == null) {
            return null;
        }
        this.inputSignal.add(inputSignal);

        ArrayList<?> ret;
        try {
            ret = this.model.step(inputSignal);
        } catch (JepException e) {
            throw new SULException(e);
        }

        var values = constructValueWithTime(ret);
        double endTime = getCurrentTime();
        return new ExtendedIOSignalPiece<>(inputSignal, values, endTime - this.signalStep, endTime);
    }

    /**
     * Run all steps of the python model by feeding inputSignal
     *
     * @param inputSignal The input signal
     * @return The output signal. The size is same as the input.
     */
    @Override
    public IOContinuousSignal<List<Double>> execute(@Nonnull Word<List<Double>> inputSignal)
            throws InterruptedException, ExecutionException {
        pre();

        @SuppressWarnings("rawtypes")
        ArrayList<?> ret = null;

        try {
            // Use exec() if it is available in the model for batch processing.
            // Otherwise, use step() for each input signal.
            if (this.model.hasExec()) {
                this.inputSignal.addAll(inputSignal);
                ret = this.model.exec(inputSignal.asList());
            } else {
                for (var e : inputSignal) {
                    this.inputSignal.add(e);
                    ret = this.model.step(e);
                }
            }
        } catch (JepException exc) {
            throw new ExecutionException(exc);
        }

        var values = constructValueWithTime(ret);

        WordBuilder<List<Double>> builder = new WordBuilder<>();
        for (int i = 0; i < inputSignal.size(); i++) {
            builder.add(values.at(i * this.signalStep));
        }
        return new IOContinuousSignal<>(inputSignal, builder.toWord(), values, this.signalStep);
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
