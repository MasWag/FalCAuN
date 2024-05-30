package net.maswag.falcaun;

import com.mathworks.engine.EngineException;
import de.learnlib.exception.SULException;
import de.learnlib.sul.SUL;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.io.Closeable;
import java.util.List;
import java.util.concurrent.ExecutionException;
/**
 * The System Under Learning implemented by a Simulink. We use the fixed step execution of Simulink to make sampling easier.
 */
@Slf4j
public class SimulinkSUL implements ContinuousNumericSUL, Closeable {
    /**
     * The simulation step of Simulink.
     * <p>
     * If this value is too large, Simulink can abort due to an computation error. In that case, you should make this value larger.
     */
    private final SimulinkModel model;

    /**
     * Setter of simulinkSimulationStep
     *
     * @param simulinkSimulationStep The fixed simulation step of Simulink. If this value is too large, Simulink can abort due to an computation error.
     */
    public void setSimulationStep(double simulinkSimulationStep) {
        this.model.setSimulationStep(simulinkSimulationStep);
    }

    public SimulinkSUL(String initScript, List<String> paramNames, Double signalStep, Double simulinkSimulationStep) throws InterruptedException, ExecutionException {
        // Load System here
        model = new SimulinkModel(initScript, paramNames, signalStep, simulinkSimulationStep);
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
        model.reset();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void post() {
        model.reset();
    }

    /**
     * {@inheritDoc}
     */
    @Nullable
    @Override
    public ExtendedIOSignalPiece<List<Double>> step(@Nullable List<Double> inputSignal) throws SULException {
        if (inputSignal == null) {
            return null;
        }
        ValueWithTime<List<Double>> value = model.step(inputSignal);

        double endTime = model.getCurrentTime();
        return new ExtendedIOSignalPiece<>(inputSignal, value, endTime - model.getSignalStep(), endTime);
    }

    /**
     * Execute the Simulink model by feeding inputSignal
     * <p>
     * For inputSignal = a1, a2, ..., an, we construct a timed word w = (a1, 0), (a2, T), (a3, 2 * T), ... (an, (n - 1) * T) and execute the Simulink model by feeding the piecewise-linear interpolation of w.
     *
     * @param inputSignal The input signal
     * @return The output signal. The size is same as the input.
     */
    @Override
    public IOContinuousSignal<List<Double>> execute(Word<List<Double>> inputSignal) throws InterruptedException, ExecutionException {
        ValueWithTime<List<Double>> values = model.execute(inputSignal);

        WordBuilder<List<Double>> builder = new WordBuilder<>();
        for (int i = 0; i < inputSignal.size(); i++) {
            builder.add(values.at(i * model.getSignalStep()));
        }

        return new IOContinuousSignal<>(inputSignal, builder.toWord(),
                values, model.getSignalStep());
    }

    /**
     * Execute the Simulink model by feeding inputSignal
     */
    public ValueWithTime<List<Double>> executeRaw(Word<List<Double>> inputSignal) throws ExecutionException, InterruptedException {
        return model.execute(inputSignal);
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
     * Close the MATLAB engine. This method must be called when the object is no longer used.
     */
    @Override
    public void close() {
        try {
            this.model.close();
        } catch (EngineException e) {
            log.warn("Failed to close the MATLAB engine: {}", e.getMessage());
        }
    }

    /**
     * {@inheritDoc}
     */
    public double getSimulationTimeSecond() {
        return this.model.getSimulationTimeSecond();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int getCounter() {
        return this.model.getCounter();
    }

    @Override
    public void clear() {
        this.model.clear();
    }
}
