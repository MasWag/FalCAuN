package org.group_mmm;

import com.mathworks.engine.MatlabEngine;
import de.learnlib.api.SUL;
import de.learnlib.api.exception.SULException;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import org.apache.commons.lang3.ArrayUtils;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.concurrent.ExecutionException;

/**
 * The Simulink SUL
 */
class SimulinkSUL implements SUL<ArrayList<Double>, ArrayList<Double>> {
    private static final Logger LOGGER = LoggerFactory.getLogger(SimulinkSUL.class);
    private final Double signalStep;
    // The simulation step of Simulink.
    private final double SIMULINK_SIMULATION_STEP = 0.0025;
    private MatlabEngine matlab;
    private ArrayList<String> paramNames;
    private Double endTime = 0.0;
    private ArrayList<ArrayList<Double>> previousInput;
    private boolean isInitial = true;

    SimulinkSUL(String initScript, ArrayList<String> paramNames, Double signalStep) throws InterruptedException, ExecutionException {
        // Load System here
        this.paramNames = paramNames;
        this.signalStep = signalStep;
        String[] engines = MatlabEngine.findMatlab();
        if (engines.length == 0) {
            matlab = MatlabEngine.startMatlab();
        } else {
            matlab = MatlabEngine.connectMatlab();
        }

        matlab.eval("clear;");
        matlab.eval("warning('off', 'Simulink:LoadSave:EncodingMismatch')");
        matlab.putVariable("signalStep", signalStep);

        matlab.eval(initScript);
    }

    static private void appendSignalStep(ArrayList<ArrayList<Double>> previousInput, ArrayList<Double> signalStep) {
        for (int i = 0; i < signalStep.size(); i++) {
            if (previousInput.size() <= i) {
                previousInput.add(new ArrayList<>());
                assert previousInput.size() == i + 1;
                previousInput.get(i).add(signalStep.get(i));
                previousInput.get(i).add(signalStep.get(i));
            } else {
                previousInput.get(i).add(signalStep.get(i));
            }
        }
    }

    @Override
    public boolean canFork() {
        return false;
    }

    @Override
    public void pre() {
        endTime = 0.0;
        previousInput = new ArrayList<>();
        isInitial = true;
    }

    @Override
    public void post() {
        previousInput.clear();
        endTime = 0.0;
        isInitial = true;
    }

    @Nullable
    @Override
    public ArrayList<Double> step(@Nullable ArrayList<Double> inputSignal) throws SULException {
        assert (isInitial && endTime == 0) || (endTime > 0.0);
        if (inputSignal == null) {
            return null;
        }
        ArrayList<Double> result;
        LOGGER.trace("Input: " + inputSignal);

        appendSignalStep(previousInput, inputSignal);
        try {
            // Make the input signal
            int numberOfSamples = (int) (endTime * 1 / signalStep) + 1;
            StringBuilder builder = new StringBuilder();
            makeDataSet(numberOfSamples, inputSignal.size(), builder);

            configureSimulink(builder);

            // Execute the simulation
            builder.append("set_param(mdl,'SaveFinalState','on','FinalStateName', 'myOperPoint','SaveCompleteFinalSimState','on');");
            if (isInitial) {
                builder.append("set_param(mdl, 'LoadInitialState', 'off');");
                isInitial = false;
            } else {
                builder.append("set_param(mdl, 'LoadInitialState', 'on');");
                builder.append("set_param(mdl, 'InitialState', 'myOperPoint');");
            }

            builder.append("simOut = sim(mdl, 'StopTime', '" + (endTime + signalStep) + "');");
            builder.append("myOperPoint = simOut.get('myOperPoint');");
            builder.append("y = simOut.get('yout');");

            matlab.eval(builder.toString());

            // get the simulation result and make the result
            double[][] y = matlab.getVariable("y");

            result = new ArrayList<>(Arrays.asList(ArrayUtils.toObject(y[y.length - 1])));
        } catch (Exception e) {
            System.out.println(e.getMessage());
            assert false;
            throw new SULException(e);
        }

        // Final internal process
        endTime += signalStep;
        assert !isInitial;
        assert endTime > 0.0;
        LOGGER.trace("Output: " + result);

        return result;
    }

    private void makeDataSet(int numberOfSamples, int signalDimension, StringBuilder builder) throws ExecutionException, InterruptedException {
        builder.append("numberOfSamples = " + numberOfSamples + ";");
        //matlab.putVariable("numberOfSamples", (double) numberOfSamples);
        builder.append("timeVector = (0:numberOfSamples) * signalStep;");
        //matlab.eval("timeVector = (0:numberOfSamples) * signalStep;");
        builder.append("ds = Simulink.SimulationData.Dataset;");
        //matlab.eval("ds = Simulink.SimulationData.Dataset;");
        for (int i = 0; i < signalDimension; i++) {
            double[] tmp = previousInput.get(i).stream().mapToDouble(Double::doubleValue).toArray();
            matlab.putVariable("tmp" + i, tmp);
            builder.append("input" + i + " = timeseries(tmp" + i + ", timeVector);");
            //matlab.eval("input = timeseries(tmp, timeVector);");
            builder.append("ds = ds.addElement(input" + i + ", '" + paramNames.get(i) + "');");
            //matlab.eval("ds = ds.addElement(input, '" + paramNames.get(i) + "');");
        }
    }

    private void configureSimulink(StringBuilder builder) throws InterruptedException, ExecutionException {
        // We use the data in ds
        builder.append("set_param(mdl, 'LoadExternalInput', 'on');");
        builder.append("set_param(mdl, 'ExternalInput', 'ds');");

        // Enable fast restart
        builder.append("set_param(mdl,'FastRestart','on');");

        /// Configuration on the accelerator
        // Use normal mode
        builder.append("set_param(mdl,'SimulationMode','normal');");
        // Enable accelerator mode
        //matlab.eval("set_param(mdl,'SimulationMode','accelerator');");
        // Enable classic accelerator mode
        //matlab.eval("set_param(0, 'GlobalUseClassicAccelMode', 'on');");


        // The save format must be an array
        builder.append("set_param(mdl, 'SaveFormat', 'Array');");

        // Configuration on the decimation
        builder.append("set_param(mdl,  'SolverType', 'Fixed-step');");
        builder.append("set_param(mdl, 'FixedStep', '" + SIMULINK_SIMULATION_STEP + "');");
        builder.append("set_param(mdl, 'Decimation', '" + (signalStep / SIMULINK_SIMULATION_STEP) + "');");
        // matlab.eval("set_param(mdl, 'Decimation', '" + (1) + "');");
    }

    /**
     * @param inputSignal The input signal
     * @return The output signal. The size is same as the input.
     */
    Word<ArrayList<Double>> execute(Word<ArrayList<Double>> inputSignal) throws InterruptedException, ExecutionException {
        assert (isInitial && endTime == 0) || (endTime > 0.0);
        if (inputSignal == null) {
            return null;
        }

        pre();
        final int numberOfSamples = inputSignal.length();
        final int signalDimension = paramNames.size();
        for (ArrayList<Double> signalStep : inputSignal) {
            appendSignalStep(previousInput, signalStep);
        }
        StringBuilder builder = new StringBuilder();

        makeDataSet(numberOfSamples, signalDimension, builder);

        configureSimulink(builder);

        // Execute the simulation
        builder.append("set_param(mdl, 'LoadInitialState', 'off');");
        builder.append("simOut = sim(mdl, 'StopTime', '" + (signalStep * numberOfSamples) + "');");
        builder.append("y = simOut.get('yout');");
        matlab.eval(builder.toString());

        // get the simulation result and make the result
        double[][] y = matlab.getVariable("y");

        //convert double[][] to Word<ArrayList<Double>
        WordBuilder<ArrayList<Double>> result = new WordBuilder<>();

        for (double[] outputStep : ArrayUtils.subarray(y, 1, y.length)) {
            result.append(new ArrayList<>(Arrays.asList(ArrayUtils.toObject(outputStep))));
        }

        post();

        assert inputSignal.size() == result.toWord().size();
        return result.toWord();
    }

    @Nonnull
    @Override
    public SUL<ArrayList<Double>, ArrayList<Double>> fork() throws UnsupportedOperationException {
        throw new UnsupportedOperationException();
    }

    @Override
    protected void finalize() throws Throwable {
        try {
            super.finalize();
        } finally {
            matlab.close();
        }
    }
}
