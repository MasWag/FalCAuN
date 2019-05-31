package org.group_mmm;

import com.mathworks.engine.MatlabEngine;
import de.learnlib.api.SUL;
import de.learnlib.api.exception.SULException;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.ArrayList;

/**
 * The Simulink SUL
 */
class SimulinkSUL implements SUL<ArrayList<Double>, ArrayList<Double>> {
    private final Double signalStep;
    private MatlabEngine matlab;
    private ArrayList<String> paramNames;
    private Double endTime = 0.0;
    private ArrayList<ArrayList<Double>> previousInput;
    private Boolean isInitial = true;

    SimulinkSUL(String initScript, ArrayList<String> paramNames, Double signalStep) throws Exception {
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
    }

    @Nullable
    @Override
    public ArrayList<Double> step(@Nullable ArrayList<Double> inputSignal) throws SULException {
        if (inputSignal == null) {
            return null;
        }
        ArrayList<Double> result = new ArrayList<>();

        for (int i = 0; i < inputSignal.size(); i++) {
            if (previousInput.size() <= i) {
                previousInput.add(new ArrayList<>());
                assert previousInput.size() == i + 1;
                previousInput.get(i).add(inputSignal.get(i));
            } else {
                previousInput.get(i).add(inputSignal.get(i));
            }
        }
        try {
            // Make the input signal
            int numberOfSamples = (int) (endTime * 1 / signalStep);
            if (numberOfSamples == 0) {
                numberOfSamples = 1;
            }
            matlab.putVariable("numberOfSamples", (double) numberOfSamples);
            matlab.eval("timeVector = (0:numberOfSamples) * signalStep;");
            matlab.eval("ds = Simulink.SimulationData.Dataset;");
            for (int i = 0; i < inputSignal.size(); i++) {
                double[] tmp = previousInput.get(i).stream().mapToDouble(Double::doubleValue).toArray();
                matlab.putVariable("tmp", tmp);
                matlab.eval("input = timeseries(tmp, timeVector);");
                matlab.eval("ds = ds.addElement(input, '" + paramNames.get(i) + "');");
            }

            // Execute the simulation
            matlab.eval("set_param(mdl, 'LoadExternalInput', 'on');");
            matlab.eval("set_param(mdl, 'ExternalInput', 'ds');");
            matlab.eval("set_param(mdl,'SaveFinalState','on','FinalStateName', 'myOperPoint','SaveCompleteFinalSimState','on');");
            if (isInitial) {
                matlab.eval("set_param(mdl, 'LoadInitialState', 'off');");
                isInitial = false;
            } else {
                matlab.eval("set_param(mdl, 'LoadInitialState', 'on');");
                matlab.eval("set_param(mdl, 'InitialState', 'myOperPoint');");
            }
            matlab.eval("simOut = sim(mdl, 'StopTime', '" + (endTime + signalStep) + "', 'SaveOutput', 'on', 'OutputSaveName', 'yOut', 'LimitDataPoints', 'off');");
            matlab.eval("myOperPoint = simOut.get('myOperPoint');");
            matlab.eval("y = simOut.get('yOut');");

            // get the simulation result and make the result
            double[][] y = matlab.getVariable("y");

            for (double[] yi : y) {
                result.add(yi[yi.length - 1]);
            }
        } catch (Exception e) {
            throw new SULException(e);
        }

        // Final internal process
        endTime += signalStep;
        return result;
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
