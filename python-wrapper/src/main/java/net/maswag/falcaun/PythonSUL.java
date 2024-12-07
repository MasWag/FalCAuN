package net.maswag.falcaun;

//import com.mathworks.engine.EngineException;
import de.learnlib.exception.SULException;
import de.learnlib.sul.SUL;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import org.uma.jmetal.problem.multiobjective.UF.UF1;

import java.io.Closeable;
import java.util.List;
import java.util.ArrayList;
import java.util.concurrent.ExecutionException;

/**
 * The System Under Learning implemented by a Simulink. We use the fixed step
 * execution of Simulink to make sampling easier.
 */
@Slf4j
public class PythonSUL implements ContinuousNumericSUL, Closeable {

    ArrayList<List<Double>> outputSignals = new ArrayList<List<Double>>();
    private final PythonModel model;

    public PythonSUL(String initScript, Double signalStep) throws InterruptedException, ExecutionException {
        this.model = new PythonModel(initScript, signalStep);
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
    public ExtendedIOSignalPiece<List<Double>> step(@Nullable List<Double> inputSignal) {
        if (inputSignal == null) {
            return null;
        }
        List<Double> outputSignal = null;
        try
        {
            outputSignal = model.step(inputSignal);
        }
        catch (Exception e)
        {
            System.out.printf("Raised error : %s\n", e.toString());
        }
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
        
        try
        {
            ValueWithTime<List<Double>> values = model.execute(inputSignal);
            /*
            System.out.println("Prnt values");
            System.out.println(values.timestamps);
            System.out.println(values.values);
            */
            WordBuilder<List<Double>> builder = new WordBuilder<>();
            for (int i = 0; i < inputSignal.size(); i++) {
                builder.add(values.at(i * model.getSignalStep()));
            }

            //System.out.println("Exec Values");
            //System.out.println(values.toString());
            return new IOContinuousSignal<>(inputSignal, builder.toWord(), values, model.getSignalStep());
        }
        catch (Exception e)
        {
            //assert false; //利かない!?
            System.out.printf("Raised error : %s\n", e.toString());
            throw new ExecutionException(new Throwable());
            //return new IOContinuousSignal<>(inputSignal, inputSignal, null, null);
        }
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
        /*
         * try { this.model.close(); } catch (EngineException e) {
         * log.warn("Failed to close the MATLAB engine: {}", e.getMessage()); }
         */
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
