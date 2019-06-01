package org.group_mmm;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;

class SimulinkVerifierTest {
    private final String initScript = "cd ./src/test/resources/MATLAB; initAFC;";
    private final ArrayList<String> paramNames = new ArrayList<>(Arrays.asList("Pedal Angle", "Engine Speed"));
    private final Double signalStep = 10.0;
    private SimulinkVerifier verifier;
    private ArrayList<String> properties;
    private SimulinkSULMapper mapper;

    @BeforeEach
    void setUp() {
        // [] (velocity < 30)
        properties = new ArrayList<>(Arrays.asList("[] (output == \"a\")"));

        // Construct the mapper
        ArrayList<Map<Character, Double>> inputMapper;
        ArrayList<Map<Character, Double>> outputMapper;
        ArrayList<Character> largest;

        {
            Map<Character, Double> mapper1 = new HashMap<>();
            mapper1.put('a', 00.0);
            mapper1.put('b', 80.0);
            Map<Character, Double> mapper2 = new HashMap<>();
            mapper2.put('a', 0.0);
            mapper2.put('b', 9000.0);
            inputMapper = new ArrayList<>(Arrays.asList(mapper1, mapper2));
        }
        {
            Map<Character, Double> mapper1 = new HashMap<>();
            mapper1.put('a', 10.0);
            mapper1.put('b', 20.0);
            Map<Character, Double> mapper2 = new HashMap<>();
            Map<Character, Double> mapper3 = new HashMap<>();

            outputMapper = new ArrayList<>(Arrays.asList(mapper1, mapper2, mapper3));
            largest = new ArrayList<>(Arrays.asList('c', '0', '0'));
        }
        mapper = new SimulinkSULMapper(inputMapper, largest, outputMapper);

        try {
            verifier = new SimulinkVerifier(initScript, paramNames, signalStep, properties, mapper);
        } catch (Exception e) {
            System.out.println(e.getMessage());
            assert false;
        }
    }

    @Test
    void run() {
        assertFalse(verifier.run());
        System.out.println(verifier.getCexAbstractInput());
        System.out.println(verifier.getCexOutput());
        verifier.visualize();
    }

    @Test
    void getCexProperty() {
    }

    @Test
    void getCexInput() {
    }

    @Test
    void getCexOutput() {
    }
}