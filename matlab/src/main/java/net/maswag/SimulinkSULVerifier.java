package net.maswag;

import java.util.List;

public class SimulinkSULVerifier extends NumericSULVerifier {
    /**
     * <p>Constructor for SimulinkVerifier.</p>
     *
     * @param initScript The MATLAB script called at first. You have to define mdl in the script.
     * @param paramName  The list of input parameters.
     * @param signalStep The signal step in the simulation
     * @param properties The LTL properties to be verified
     * @param mapper     The I/O mapepr between abstract/concrete Simulink models.
     * @throws java.lang.Exception It can be thrown from the constructor of SimulinkSUL.
     */
    public SimulinkSULVerifier(String initScript, List<String> paramName, double signalStep, double simulinkSimulationStep, AdaptiveSTLUpdater properties, NumericSULMapper mapper) throws Exception {
        super(new SimulinkSUL(initScript, paramName, signalStep, simulinkSimulationStep), signalStep, properties, mapper);
    }

    /**
     * Modify the simulation step of Simulink.
     *
     * @param simulinkSimulationStep The fixed simulation step of Simulink. If this value is too large, Simulink can abort due to an computation error.
     */
    public void setSimulationStep(double simulinkSimulationStep) {
        ((SimulinkSUL)this.rawSUL).setSimulationStep(simulinkSimulationStep);
    }
}
