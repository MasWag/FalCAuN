package org.group_mmm;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;

class SimulinkVerifierTest {
    private final String initScript = "cd ./src/test/resources/; initAFC;";
    private final ArrayList<String> paramNames = new ArrayList<>(Arrays.asList("Pedal Angle", "Engine Speed"));
    private final Double signalStep = 10.0;
    SimulinkVerifier verifier;
    private ArrayList<String> properties;
    private SimulinkSULMapper mapper;

    @BeforeEach
    void setUp() {
        // [] (velocity < 30)
        properties = new ArrayList<>(Arrays.asList("[] (output == \"a\")"));

        try {
            verifier = new SimulinkVerifier(initScript, paramNames, signalStep, properties, mapper);
        } catch (Exception ignored) {
            assert false;
        }

    }

    @Test
    void run() {

    }
}