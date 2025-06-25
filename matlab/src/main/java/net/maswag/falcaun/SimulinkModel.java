package net.maswag.falcaun;

import com.mathworks.engine.EngineException;
import com.mathworks.engine.MatlabEngine;
import de.learnlib.exception.SULException;
import lombok.Getter;
import lombok.Setter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.word.Word;
import org.apache.commons.lang3.ArrayUtils;

import org.jetbrains.annotations.NotNull;
import java.util.*;
import java.util.concurrent.ExecutionException;

/**
 * Raw Simulink model. We use the fixed step execution of Simulink to make sampling easier.
 */
@Slf4j
public class SimulinkModel {
    /**
     * The signal step of the input signal.
     */
    @Getter
    private final Double signalStep;
    /**
     * The simulation step of Simulink.
     * <p>
     * If this value is too large, Simulink can abort due to a computation error. In that case, you should make this value larger.
     */
    @Getter
    private double simulinkSimulationStep;
    private final MatlabEngine matlab;
    private final List<String> paramNames;
    /**
     * The current time of the simulation
     */
    public double getCurrentTime() {
        return inputSignal.duration();
    }
    private Signal inputSignal;
    private boolean isInitial = true;
    private boolean useFastRestart = true;
    @Getter
    private int counter = 0;
    private final TimeMeasure simulationTime = new TimeMeasure();
    @Setter
    private InterpolationMethod interpolationMethod = InterpolationMethod.LINEAR;

    /**
     * Setter of simulinkSimulationStep
     *
     * @param simulinkSimulationStep The fixed simulation step of Simulink. If this value is too large, Simulink can abort due to an computation error.
     */
    public void setSimulationStep(double simulinkSimulationStep) {
        this.simulinkSimulationStep = simulinkSimulationStep;
    }

    public SimulinkModel(String initScript, List<String> paramNames, Double signalStep, Double simulinkSimulationStep) throws InterruptedException, ExecutionException {
        // Load System here
        this.paramNames = paramNames;
        this.signalStep = signalStep;
        this.simulinkSimulationStep = simulinkSimulationStep;
        String[] engines = MatlabEngine.findMatlab();
        if (engines.length == 0) {
            matlab = MatlabEngine.startMatlab();
        } else {
            matlab = MatlabEngine.connectMatlab();
        }

        matlab.eval("clear;");
        matlab.eval("warning('off', 'Simulink:LoadSave:EncodingMismatch')");
        matlab.putVariable("signalStep", signalStep);
        try {
            matlab.eval(initScript);
        } catch (Exception e) {
            log.error("An error occurred during running the initial script. This also happens if the engine is not correctly installed.");
            log.error("Init Script: {}", initScript);
            throw e;
        }
        // Initialize the current state
        this.reset();
    }

    /**
     * Reset the Simulink model to the initial state.
     */
    public void reset() {
        inputSignal = new Signal(signalStep);
        isInitial = true;
    }

    /**
     * Clear the counter and the time measure.
     */
    public void clear() {
        counter = 0;
        simulationTime.reset();
    }

    /**
     * Execute the Simulink model for one step by feeding inputSignal
     * @param inputSignal The input signal
     * @return The output signal with timestamps of the entire execution.
     */
    @NotNull
    public ValueWithTime<List<Double>> step(@NotNull List<Double> inputSignal) {
        if (this.isInitial) {
            counter++;
        }
        assert isInitial || !inputSignal.isEmpty();
        List<List<Double>> result = new ArrayList<>();
        List<Double> timestamps;
        log.trace("Input: {}", inputSignal);

        this.inputSignal.add(inputSignal);
         // For efficiency, we use StringBuilder to make the entire script to execute in MATLAB rather than evaluate each line.
        StringBuilder builder = new StringBuilder();
        try {
            // Make the input signal
            makeDataSet(builder);

            configureSimulink(builder);
            preventHugeTempFile(builder);

            // Execute the simulation
            builder.append("set_param(mdl,'SaveFinalState','on','FinalStateName', 'myOperPoint','SaveCompleteFinalSimState','on');");
            if (isInitial) {
                builder.append("set_param(mdl, 'LoadInitialState', 'off');");
                isInitial = false;
            } else {
                builder.append("set_param(mdl, 'LoadInitialState', 'on');");
                builder.append("set_param(mdl, 'InitialState', 'myOperPoint');");
            }

            // Run the simulation
            runSimulation(builder, this.inputSignal.duration());

            simulationTime.start();
            matlab.eval(builder.toString());
            simulationTime.stop();

            // get the simulation result and make the result
            double[][] y = this.getResult();
            double[] t = this.getTimestamps();
            assert(t.length == y.length);

            // convert double[][] to List<List<Double>>
            for (double[] outputStep: y) {
                result.add(Arrays.asList(ArrayUtils.toObject(outputStep)));
            }

            // convert double[] to List<Double>
            timestamps = Arrays.asList(ArrayUtils.toObject(t));
        } catch (Exception e) {
            log.error("There was an error in the simulation: {}", e.getMessage());
            log.error("The executed script was: {}", builder);
            assert false;
            throw new SULException(e);
        }

        // Final internal process
        assert !isInitial;
        log.trace("Output: {}", result);

        return new ValueWithTime<>(timestamps, result);
    }

    private void makeDataSet(StringBuilder builder) throws ExecutionException, InterruptedException {
        builder.append("timeVector = ").append(inputSignal.getTimestamps()).append(";");
        builder.append("ds = Simulink.SimulationData.Dataset;");
        for (int i = 0; i < inputSignal.dimension(); i++) {
            double[] tmp = inputSignal.dimensionGet(i).stream().mapToDouble(Double::doubleValue).toArray();
            matlab.putVariable("tmp" + i, tmp);
            builder.append("input").append(i).append(" = timeseries(tmp").append(i).append(", timeVector);");
            if (this.interpolationMethod == InterpolationMethod.CONSTANT) {
                // Set the interpolation method to zoh https://jp.mathworks.com/help/matlab/ref/timeseries.setinterpmethod.html
                //builder.append("input").append(i).append(" = setinterpmethod(input").append(i).append(", 'zoh');");
                builder.append("input").append(i).append(".DataInfo.Interpolation = tsdata.interpolation('zoh');");
            } else {
                // Set the interpolation method to linear https://jp.mathworks.com/help/matlab/ref/timeseries.setinterpmethod.html
                //builder.append("input").append(i).append(" = setinterpmethod(input").append(i).append(", 'linear');");
                builder.append("input").append(i).append(".DataInfo.Interpolation = tsdata.interpolation('linear');");
            }
            builder.append("ds = ds.addElement(input").append(i).append(", '").append(paramNames.get(i)).append("');");
        }
    }

    private void configureSimulink(StringBuilder builder) {
        // We use the data in ds
        builder.append("set_param(mdl, 'LoadExternalInput', 'on');");
        builder.append("set_param(mdl, 'ExternalInput', 'ds');");

        // Enable fast restart
        if (this.useFastRestart) {
            builder.append("set_param(mdl,'FastRestart','on');");
        } else {
            builder.append("set_param(mdl,'FastRestart','off');");
        }

        /// Configuration on the accelerator
        // Use normal mode
        // builder.append("set_param(mdl,'SimulationMode','normal');");
        // Enable accelerator mode
        builder.append("set_param(mdl,'SimulationMode','accelerator');");
        // Enable classic accelerator mode
        builder.append("set_param(0, 'GlobalUseClassicAccelMode', 'on');");


        // The save format must be an array
        builder.append("set_param(mdl, 'SaveFormat', 'Array');");
        // We save the output as yout
        builder.append("set_param(mdl, 'SaveOutput', 'on');");
        builder.append("set_param(mdl, 'OutputSaveName', 'yout');");
        // We save the time as tout
        builder.append("set_param(mdl, 'SaveTime', 'on');");
        builder.append("set_param(mdl, 'TimeSaveName', 'tout');");

        // Configuration on the decimation
        builder.append("set_param(mdl, 'SolverType', 'Fixed-step');");
        builder.append("set_param(mdl, 'FixedStep', '").append(simulinkSimulationStep).append("');");
        // We dump all the results
        builder.append("set_param(mdl, 'LimitDataPoints', 'off');");
        // We do not decimate the result
        // builder.append("set_param(mdl, 'Decimation', '").append(signalStep / simulinkSimulationStep).append("');");
    }

    private void preventHugeTempFile(StringBuilder builder) {
        builder.append("Simulink.sdi.setAutoArchiveMode(false);");
        builder.append("Simulink.sdi.setArchiveRunLimit(0);");
        builder.append("Simulink.sdi.clear;");
    }

    private void runSimulation(StringBuilder builder, double stopTime) {
        // append the input signal
        builder.append("in = Simulink.SimulationInput(mdl);");
        builder.append("in = in.setExternalInput(ds);");

        // Set the StopTime
        builder.append("in = in.setModelParameter('StopTime', '").append(stopTime).append("');");
        // Save the output to yout
        if (!this.useFastRestart) {
            builder.append("in = in.setModelParameter('SaveOutput', 'on');");
            builder.append("in = in.setModelParameter('OutputSaveName', 'yout');");
            builder.append("in = in.setModelParameter('SaveTime', 'on');");
            builder.append("in = in.setModelParameter('TimeSaveName', 'tout');");
        }
        builder.append("in = in.setModelParameter('LoadInitialState', 'off');");

        // Execute the simulation
        builder.append("simOut = sim(in);");
        // We handle the output as double.
        builder.append("y = double(simOut.get('yout'));");
        builder.append("t = double(simOut.get('tout'));");
    }

    protected double[][] getResult() throws ExecutionException, InterruptedException {
        double[][] y;
        try {
            matlab.eval("ySize = size(y);");
            double[] ySize = matlab.getVariable("ySize");
            if (this.inputSignal.duration() == 0.0) {
                double[] tmpY;
                if (ySize[1] == 1.0) {
                    // When the output is one dimensional, we need to convert it to 1D array first.
                    double tmp = matlab.getVariable("y");
                    tmpY = new double[]{tmp};
                } else {
                    tmpY = matlab.getVariable("y");
                }
                if (Objects.isNull(tmpY)) {
                    log.error("The simulation output is null");
                    y = null;
                } else {
                    y = new double[][]{tmpY};
                }
            } else {
                if (ySize[1] == 1.0) {
                    // When the output is one dimensional, we need to convert it to 2D array.
                    double[] tmpY = matlab.getVariable("y");
                    y = Arrays.stream(tmpY).mapToObj(d -> new double[]{d}).toArray(double[][]::new);
                } else {
                    y = matlab.getVariable("y");
                }
            }
        } catch (Exception e) {
            log.error("There was an error when obtaining the result: {}", e.getMessage());
            throw e;
        }
        return y;
    }

    protected double[] getTimestamps() throws ExecutionException, InterruptedException {
        double[] t;
        try {
            if (this.inputSignal.duration() == 0.0) {
                t = new double[]{0.0};
            } else {
                t = matlab.getVariable("t");
            }
        } catch (Exception e) {
            log.error("There was an error when obtaining the timestamps: {}", e.getMessage());
            throw e;
        }
        return t;
    }

    /**
     * Execute the Simulink model by feeding inputSignal
     * <p>
     * For inputSignal = a1, a2, ..., an, we construct a timed word w = (a1, 0), (a2, T), (a3, 2 * T), ... (an, (n - 1) * T) and execute the Simulink model by feeding the piecewise-linear interpolation of w.
     *
     * @param inputSignal The input signal
     * @return The output signal. The size is same as the input.
     */
    public ValueWithTime<List<Double>> execute(Word<List<Double>> inputSignal) throws InterruptedException, ExecutionException {
        if (this.isInitial) {
            counter++;
        }
        assert isInitial || !inputSignal.isEmpty();
        if (inputSignal == null) {
            return null;
        }
        reset();
        this.inputSignal.addAll(inputSignal);

        // For efficiency, we use StringBuilder to make the entire script to execute in MATLAB rather than evaluate each line.
        StringBuilder builder = new StringBuilder();

        makeDataSet(builder);

        configureSimulink(builder);

        preventHugeTempFile(builder);

        runSimulation(builder, this.inputSignal.duration());

        simulationTime.start();
        log.trace(builder.toString());
        matlab.eval(builder.toString());
        simulationTime.stop();

        // get the simulation result and make the result
        double[][] y = this.getResult();
        double[] t = this.getTimestamps();
        if (Objects.isNull(y) || Objects.isNull(y[0])) {
            if (this.useFastRestart) {
                this.useFastRestart = false;
                log.info("disable fast restart");
                return this.execute(inputSignal);
            } else {
                log.error("I do not know how to obtain non-null result");
                return null;
            }
        }
        assert(t.length == y.length);

        // convert double[][] to List<List<Double>>
        List<List<Double>> result = new ArrayList<>();
        for (double[] outputStep: y) {
            result.add(Arrays.asList(ArrayUtils.toObject(outputStep)));
        }

        reset();
        return new ValueWithTime<>(Arrays.asList(ArrayUtils.toObject(t)), result);
    }

    /**
     * Close the MATLAB engine. This method must be called when the object is no longer used.
     */
    public void close() throws EngineException {
        matlab.close();
    }

    public double getSimulationTimeSecond() {
        return this.simulationTime.getSecond();
    }

    /**
     * Enum for the interpolation methods of the input signal
     */
    public enum InterpolationMethod {
        /**
         * Piecewise constant interpolation
         * Note: This is not supported in the current version.
         */
        CONSTANT,
        /**
         * Piecewise linear interpolation
         */
        LINEAR
    }
}
