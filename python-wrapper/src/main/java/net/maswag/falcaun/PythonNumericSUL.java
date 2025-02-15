package net.maswag.falcaun;

import de.learnlib.sul.SUL;
import jep.JepException;
import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import java.io.Closeable;
import java.util.List;
import java.util.ArrayList;
import java.util.concurrent.ExecutionException;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * The System Under Learning implemented by a Simulink. We use the fixed step
 * execution of Simulink to make sampling easier.
 */
@Slf4j
public class PythonNumericSUL implements NumericSUL, Closeable {
    /**
     * The signal step of the input signal.
     */
    protected final Double signalStep;
    @SuppressWarnings("rawtypes")
    protected final PythonModel<List<Double>, ArrayList> model;
    protected Signal inputSignal = null;
    protected ArrayList<List<Double>> outputSignals = new ArrayList<List<Double>>();
    protected final TimeMeasure simulationTime = new TimeMeasure();

    @Getter
    private int counter = 0;

    @SuppressWarnings("rawtypes")
    public PythonNumericSUL(String initScript, Double signalStep) throws InterruptedException, ExecutionException {
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
        simulationTime.reset();
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

    @Nullable
    public ExtendedIOSignalPiece<List<Double>> step_aux(@Nullable List<Double> inputSignal) {
        if (inputSignal == null) {
            return null;
        }
        this.inputSignal.add(inputSignal);

        simulationTime.start();
        var ret = this.model.step(inputSignal);
        simulationTime.stop();

        Stream<?> stream = ret.stream();
        var outputSignal = stream.map(e -> Double.class.cast(e)).collect(Collectors.toList());
        this.outputSignals.add(outputSignal);
        return new ExtendedIOSignalPiece<>(inputSignal, outputSignal, outputSignals);
    }

    /**
     * {@inheritDoc}
     */
    @Nullable
    @Override
    public IOSignalPiece<List<Double>> step(@Nullable List<Double> inputSignal) {
        return step_aux(inputSignal);

    }

    public IOContinuousSignal<List<Double>> execute_aux(Word<List<Double>> inputSignal)
            throws InterruptedException, ExecutionException {
        pre();

        ArrayList<List<Double>> outputs = new ArrayList<List<Double>>();
        ArrayList<Double> timestamps = new ArrayList<Double>();
        ArrayList<?> ret;

        for (var e : inputSignal) {
            this.inputSignal.add(e);

            simulationTime.start();
            try {
                ret = this.model.step(e);
            } catch (JepException exc) {
                throw new InterruptedException(exc.toString());
            }
            simulationTime.stop();

            Stream<?> stream = ret.stream();
            var output = stream.map(obj -> Double.class.cast(obj)).collect(Collectors.toList());
            outputs.add(output);
            timestamps.add(this.getCurrentTime());
        }

        ValueWithTime<List<Double>> values = new ValueWithTime<>(timestamps, outputs);
        WordBuilder<List<Double>> builder = new WordBuilder<>();
        for (int i = 0; i < inputSignal.size(); i++) {
            builder.add(values.at(i * this.signalStep));
        }
        return new IOContinuousSignal<>(inputSignal, builder.toWord(), values, this.signalStep);
    }

    /**
     * Execute the Simulink model by feeding inputSignal
     * <p>
     * For inputSignal = a1, a2, ..., an, we construct a timed word w = (a1, 0),
     * (a2, T), (a3, 2 * T), ... (an, (n - 1) * T) and execute the Simulink model by
     * feeding the piecewise-linear interpolation of w.
     *
     * @param inputSignal The input signal
     * @return The output signal. The size is same as the input.
     */
    @Override
    public IOSignal<List<Double>> execute(Word<List<Double>> inputSignal)
            throws InterruptedException, ExecutionException {
        return execute_aux(inputSignal);
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
     * Close the MATLAB engine. This method must be called when the object is no
     * longer used.
     */
    @Override
    public void close() {
        this.model.close();
    }

    /**
     * {@inheritDoc}
     */
    public double getSimulationTimeSecond() {
        return this.simulationTime.getSecond();
    }
}
