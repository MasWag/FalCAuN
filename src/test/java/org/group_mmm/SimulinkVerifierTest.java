package org.group_mmm;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.*;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

class SimulinkVerifierTest {
    private final String initScript = "cd ./src/test/resources/MATLAB; initAFC;";
    /*
       The range should be as follows.
	  - Pedal_Angle: [8.8 90.0]
      - Engine_Speed: [900.0 1100.0]
     */
    private final ArrayList<String> paramNames = new ArrayList<>(Arrays.asList("Pedal Angle", "Engine Speed"));
    private final Double signalStep = 10.0;
    private SimulinkVerifier verifier;
    private ArrayList<String> properties;
    private SimulinkSULMapper mapper;
    private ArrayList<Function<ArrayList<Double>, Double>> sigMap = new ArrayList<>();


    @BeforeEach
    void setUp() {
        // [] (velocity < 30)
        properties = new ArrayList<>(Collections.singletonList("[] (output == \"a00\")"));

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
        mapper = new SimulinkSULMapper(inputMapper, largest, outputMapper, sigMap);

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
    }

    @Test
    void getCexProperty() {
        assertFalse(verifier.run());
        String expected = "[] (output == \"a00\")";
        assertEquals(expected, verifier.getCexProperty());
    }

    @Test
    void getCexInput() {
    }

    @Test
    void getCexOutput() {
    }
}