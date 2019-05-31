package org.group_mmm;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;

class SimulinkSULTest {
    private final String initScript = "cd ./src/test/resources/MATLAB; initAFC;";
    private final ArrayList<String> paramNames = new ArrayList<>(Arrays.asList("Pedal Angle", "Engine Speed"));
    private final Double signalStep = 10.0;
    private SimulinkSUL sul;

    SimulinkSULTest() throws Exception {
        this.sul = new SimulinkSUL(initScript, paramNames, signalStep);
    }

    @Test
    void canFork() {
        assertFalse(sul.canFork());
    }

    @Test
    void pre() {
        sul.pre();
    }

    @Test
    void post() {
        sul.pre();
        sul.post();
    }

    @Test
    void step() {
        sul.pre();
        ArrayList<Double> input = new ArrayList<>(Arrays.asList(80.0, 900.0));
        sul.step(input);
        input = new ArrayList<>(Arrays.asList(85.0, 920.0));
        sul.step(input);
    }

    @Test
    void fork() {
        assertThrows(UnsupportedOperationException.class, () -> sul.fork());
    }
}