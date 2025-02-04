package net.maswag.falcaun;

import de.learnlib.sul.SUL;
import lombok.extern.slf4j.Slf4j;

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
public class PythonSUL implements SUL<List<Double>, IOSignalPiece<List<Double>>>, Closeable {
    /**
     * The signal step of the input signal.
     */
    private final Double signalStep;
    ArrayList<List<Double>> outputSignals = new ArrayList<List<Double>>();
    private final PythonModel model;
    private final TimeMeasure simulationTime = new TimeMeasure();

    public PythonSUL(String initScript, Double signalStep) throws InterruptedException, ExecutionException {
        this.model = new PythonModel(initScript);
        this.signalStep = signalStep;
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
     * {@inheritDoc}
     */
    @Override
    public void pre() {
        inputSignal = new Signal(signalStep);
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
    public IOSignalPiece<List<Double>> step(@Nullable List<Double> inputSignal) {
        if (inputSignal == null) {
            return null;
        }
        List<Double> outputSignal = null;
        this.inputSignal.add(inputSignal);
        simulationTime.start();
        try {
            ArrayList<Double> ret = this.model.step(inputSignal);
            outputSignal = ret;
        } catch (Exception e) {
            System.out.printf("Raised error : %s\n", e.toString());
        }
        simulationTime.stop();
        this.outputSignals.add(outputSignal);

        return new ExtendedIOSignalPiece<>(inputSignal, outputSignal, outputSignals);
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
}
