package org.group_mmm;

import com.mathworks.engine.MatlabEngine;

class SimulinkSUL {
    static void start(String initScript, String breachPath) throws Exception {
        MatlabEngine matlab = MatlabEngine.connectMatlab();

        matlab.eval("addpath('" + breachPath + "')");
        matlab.eval("clear; InitBreach");
        matlab.eval("warning('off', 'Simulink:LoadSave:EncodingMismatch')");

        matlab.eval(initScript);
    }
}
