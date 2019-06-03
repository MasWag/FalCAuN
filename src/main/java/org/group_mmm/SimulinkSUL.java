package org.group_mmm;

import com.mathworks.engine.EngineException;
import com.mathworks.engine.MatlabEngine;
import de.learnlib.api.SUL;
import de.learnlib.api.exception.SULException;
import org.apache.commons.lang3.ArrayUtils;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.concurrent.ExecutionException;

/**
 * The Simulink SUL
 */
class SimulinkSUL implements SUL<ArrayList<Double>, ArrayList<Double>> {
    private final Double signalStep;
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
        assert (isInitial && endTime == 0) || (endTime > 0.0);
        if (inputSignal == null) {
            return null;
        }
        ArrayList<Double> result;

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
            // Enable fast restart
            matlab.eval("set_param(mdl,'FastRestart','on');");
            // Enable accelerator mode
            matlab.eval("set_param(mdl,'SimulationMode','accelerator')");
            // Enable classic accelerator mode
            //matlab.eval("set_param(mdl, 'GlobalUseClassicAccelMode', 'on');");
            // The save format must be an array
            matlab.eval("set_param(mdl, 'SaveFormat', 'Array');");

            if (isInitial) {
                matlab.eval("set_param(mdl, 'LoadInitialState', 'off');");
                isInitial = false;
            } else {
                matlab.eval("set_param(mdl, 'LoadInitialState', 'on');");
                matlab.eval("set_param(mdl, 'InitialState', 'myOperPoint');");
            }
            matlab.eval("simOut = sim(mdl, 'StopTime', '" + (endTime + signalStep) + "');");
            matlab.eval("myOperPoint = simOut.get('myOperPoint');");
            matlab.eval("y = simOut.get('yout');");

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
