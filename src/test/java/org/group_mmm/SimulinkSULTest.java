package org.group_mmm;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.*;

class SimulinkSULTest {
    private final String initScript = "cd ./src/test/resources/MATLAB; initAFC;";
    private final ArrayList<String> paramNames = new ArrayList<>(Arrays.asList("Pedal Angle", "Engine Speed"));
    private final Double signalStep = 10.0;
    private SimulinkSUL sul;
    // TODO: check what is the content of the three values. (I guess AF, AFref, mode)
    private int expectedOutputSize = 3;

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
        ArrayList<Double> output = sul.step(input);
        assertNotNull(output);
        assertEquals(expectedOutputSize, output.size());

        input = new ArrayList<>(Arrays.asList(85.0, 920.0));
        output = sul.step(input);
        assertNotNull(output);
        assertEquals(expectedOutputSize, output.size());
    }

    @Test
    void fork() {
        assertThrows(UnsupportedOperationException.class, () -> sul.fork());
    }
}