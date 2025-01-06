package net.maswag.falcaun;

import jep.JepConfig;
import jep.JepException;
import jep.SharedInterpreter;
import jep.python.PyCallable;
import jep.python.PyObject;
import lombok.Getter;
import lombok.Setter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.word.Word;
import org.apache.commons.lang3.ArrayUtils;
//import org.junit.rules.ExternalResource;

import javax.annotation.Nonnull;

import java.io.OutputStream;
import java.util.*;
//import java.util.concurrent.ExecutionException;
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
    private final PyObject pysul;
    public PythonModel(String initScript, Double signalStep) throws JepException {
        SharedInterpreter.setConfig(new JepConfig().redirectStdout(System.out).redirectStdErr(System.err));
        this.interpreter = new SharedInterpreter();
        this.signalStep = signalStep;

        this.interpreter.runScript(initScript);
        //this.interpreter.eval(String.format("import %s as s", moduleName));
        this.interpreter.eval("sul = SUL()");
        this.pysul = this.interpreter.getValue("sul", PyObject.class);


        // Initialize the current state
        this.reset();
    }

    /**
     * Reset the Simulink model to the initial state.
     */
    public void reset() {
        inputSignal = new Signal(signalStep);
        //this.interpreter.invoke("SUL.reset");
        PyCallable pyReset = this.pysul.getAttr("reset", PyCallable.class);
        pyReset.call();
    }

    /**
     * Clear the counter and the time measure.
     */
    public void clear() {
        simulationTime.reset();
    }

    public ArrayList<Double> origin() {
        var ref = new ArrayList<Double>();
        PyCallable pyOrigin = this.pysul.getAttr("origin", PyCallable.class);
        ArrayList<Double> ret = pyOrigin.callAs(ref.getClass());
        return ret;
    }

    /**
     * Execute the Simulink model for one step by feeding inputSignal
     * @param inputSignal The input signal
     * @return The output signal with timestamps of the entire execution.
     */
    @Nonnull @SuppressWarnings("unchecked")
    public List<Double> step(@Nonnull List<Double> inputSignal) throws Exception {
        System.out.println("Step");
        this.inputSignal.add(inputSignal);
        PyCallable pyStep = this.pysul.getAttr("step", PyCallable.class);

        var ref = new ArrayList<Double>();
        /*
        var ret = pyStep.call(inputSignal);
        System.out.println(ret.getClass().toString());
        System.out.println(ret.toString());


        var ret1 = pyStep.callAs(ref.getClass(), inputSignal);
        System.out.println(ret1.getClass().toString());
        */

        ArrayList<Double> ret0 = pyStep.callAs(ref.getClass(), inputSignal);
        System.out.println(ret0.getClass().toString());
        return ret0;
        /*
        if (ret instanceof ArrayList al)
        {
            return (ArrayList<Double>)al;
        }
        else
            throw new Exception();
            */
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
        outputs.add(origin());
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
        PyCallable pyClose = this.pysul.getAttr("close", PyCallable.class);

        pyClose.call();
        //this.interpreter.invoke("close");
    }

    public double getSimulationTimeSecond() {
        return this.simulationTime.getSecond();
    }

}
