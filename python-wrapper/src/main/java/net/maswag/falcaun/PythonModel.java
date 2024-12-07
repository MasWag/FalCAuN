package net.maswag.falcaun;

import jep.JepException;
import jep.SharedInterpreter;
import lombok.Getter;
import lombok.Setter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.word.Word;
import org.apache.commons.lang3.ArrayUtils;
import org.junit.rules.ExternalResource;

import javax.annotation.Nonnull;
import java.util.*;
import java.util.concurrent.ExecutionException;
import java.util.stream.Collectors;

import jep.SharedInterpreter;

/**
 * Raw Simulink model. We use the fixed step execution of Simulink to make sampling easier.
 */
@Slf4j
public class PythonModel {
    /**
     * The signal step of the input signal.
     */
    @Getter
    private final Double signalStep;

    /**
     * The current time of the simulation
     */
    public double getCurrentTime() {
        return inputSignal.duration();
    }
    private Signal inputSignal;
    @Getter
    private int counter = 0;
    private final TimeMeasure simulationTime = new TimeMeasure();


    private final SharedInterpreter interpreter;
    public PythonModel(String initScript, Double signalStep) throws JepException {
        this.interpreter = new SharedInterpreter();
        this.interpreter.runScript(initScript);
        this.signalStep = signalStep;

        // Initialize the current state
        this.reset();
    }

    /**
     * Reset the Simulink model to the initial state.
     */
    public void reset() {
        inputSignal = new Signal(signalStep);
        this.interpreter.invoke("SUL.reset");
    }

    /**
     * Clear the counter and the time measure.
     */
    public void clear() {
        simulationTime.reset();
    }

    /**
     * Execute the Simulink model for one step by feeding inputSignal
     * @param inputSignal The input signal
     * @return The output signal with timestamps of the entire execution.
     */
    @Nonnull @SuppressWarnings("unchecked")
    public List<Double> step(@Nonnull List<Double> inputSignal) throws Exception {
        this.inputSignal.add(inputSignal);
        Object ret = this.interpreter.invoke("SUL.step", inputSignal);
        if (ret instanceof ArrayList al)
        {
            return (ArrayList<Double>)al;
        }
        else
            throw new Exception();
    }


    /**
     * Execute the Simulink model by feeding inputSignal
     * <p>
     * For inputSignal = a1, a2, ..., an, we construct a timed word w = (a1, 0), (a2, T), (a3, 2 * T), ... (an, (n - 1) * T) and execute the Simulink model by feeding the piecewise-linear interpolation of w.
     *
     * @param inputSignal The input signal
     * @return The output signal. The size is same as the input.
     */
    public ValueWithTime<List<Double>> execute(Word<List<Double>> inputSignal) throws Exception {
        reset();
        this.inputSignal.addAll(inputSignal);


        ArrayList<List<Double>> outputs = new ArrayList<List<Double>>();
        ArrayList<Double> timestamps = new ArrayList<Double>();
        for(var e : inputSignal)
        {
            outputs.add(step(e));
            timestamps.add(this.getCurrentTime());
        }

        return new ValueWithTime<>(timestamps, outputs);
    }

    /**
     * Close the MATLAB engine. This method must be called when the object is no longer used.
     */
    public void close() {
        this.interpreter.invoke("close");
    }

    public double getSimulationTimeSecond() {
        return this.simulationTime.getSecond();
    }

}
