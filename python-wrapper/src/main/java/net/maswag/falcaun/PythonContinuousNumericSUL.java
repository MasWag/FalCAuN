package net.maswag.falcaun;

import jep.python.PyCallable;
import de.learnlib.exception.SULException;
import de.learnlib.sul.SUL;
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

/**
 * The System Under Learning implemented by a Simulink. We use the fixed step
 * execution of Simulink to make sampling easier.
 */
@Slf4j
public class PythonContinuousNumericSUL implements ContinuousNumericSUL, Closeable {
    /**
     * The signal step of the input signal.
     */
    private final Double signalStep;
    ArrayList<List<Double>> outputSignals = new ArrayList<List<Double>>();
    private final PythonModel model;
    private final PyCallable pyPre, pyPost, pyStep, pyClose;
    private final TimeMeasure simulationTime = new TimeMeasure();

    @Getter
    private int counter = 0;

    public PythonContinuousNumericSUL(String initScript, Double signalStep)
            throws InterruptedException, ExecutionException {
        this.model = new PythonModel(initScript);
        this.signalStep = signalStep;
        this.pyPre = this.model.getPysul().getAttr("pre", PyCallable.class);
        this.pyPost = this.model.getPysul().getAttr("post", PyCallable.class);
        this.pyStep = this.model.getPysul().getAttr("step", PyCallable.class);
        this.pyClose = this.model.getPysul().getAttr("close", PyCallable.class);
    }

    private Signal inputSignal;

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
        pyPre.call();
        counter++;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void post() {
        pyPost.call();
    }

    /**
     * {@inheritDoc}
     */
    @Nullable
    @Override
    public ExtendedIOSignalPiece<List<Double>> step(@Nullable List<Double> inputSignal) {
        if (inputSignal == null) {
            return null;
        }
        List<Double> outputSignal = null;
        this.inputSignal.add(inputSignal);
        simulationTime.start();
        try {
            ArrayList<Double> ret = this.pyStep.callAs(new ArrayList<Double>().getClass(), inputSignal);
            outputSignal = ret;
        } catch (Exception e) {
            System.out.printf("Raised error : %s\n", e.toString());
        }
        simulationTime.stop();
        this.outputSignals.add(outputSignal);

        return new ExtendedIOSignalPiece<>(inputSignal, outputSignal, outputSignals);

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
    public IOContinuousSignal<List<Double>> execute(Word<List<Double>> inputSignal)
            throws InterruptedException, ExecutionException {
        pre();

        ArrayList<List<Double>> outputs = new ArrayList<List<Double>>();
        ArrayList<Double> timestamps = new ArrayList<Double>();
        // outputs.add(origin());
        // timestamps.add(0.0);
        for (var e : inputSignal) {
            try {
                ArrayList<Double> ret = this.pyStep.callAs(new ArrayList<Double>().getClass(), inputSignal);
                outputs.add(ret);
            } catch (Exception exc) {
                // assert false; //利かない!?
                System.out.printf("Raised error : %s\n", exc.toString());
                throw new ExecutionException(new Throwable());
                // return new IOContinuousSignal<>(inputSignal, inputSignal, null, null);
            }
            timestamps.add(this.getCurrentTime());
        }
        ValueWithTime<List<Double>> values = new ValueWithTime<>(timestamps, outputs);
        ;
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
     * Close the MATLAB engine. This method must be called when the object is no
     * longer used.
     */
    @Override
    public void close() {
        pyClose.call();
    }

    /**
     * {@inheritDoc}
     */
    public double getSimulationTimeSecond() {
        return this.simulationTime.getSecond();
    }
}
