package org.group_mmm;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import java.util.*;
import java.util.function.Function;

import static java.lang.Math.abs;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

class SimulinkVerifierTest {
    private final String PWD = System.getenv("PWD");
    private final String initScript = "cd " + PWD + "/src/test/resources/MATLAB; initAFC;";
    /*
       The range should be as follows.
	  - Pedal_Angle: [8.8 90.0]
      - Engine_Speed: [900.0 1100.0]
     */
    private final List<String> paramNames = new ArrayList<>(Arrays.asList("Pedal Angle", "Engine Speed"));
    private final Double signalStep = 10.0;
    private SimulinkVerifier verifier;
    private List<String> properties;
    private SimulinkSULMapper mapper;
    private List<Function<List<Double>, Double>> sigMap = new ArrayList<>();
    private List<String> propertyZHA19_AFC1 = new ArrayList<>(Collections.singletonList("X [] (output == \"a00l\" || output == \"a01l\" || output == \"a01h\" || output == \"b00l\" || output == \"b01l\" || output == \"b01h\" || output == \"b00l\" || output == \"b01l\" || output == \"b01h\"|| output == \"c00l\" || output == \"c01l\" || output == \"c01h\")"));


    @BeforeEach
    void setUp() {
        // [] (velocity < 30)
        properties = new ArrayList<>(Collections.singletonList("[] (output == \"a00\")"));

        // Construct the mapper
        List<Map<Character, Double>> inputMapper;
        List<Map<Character, Double>> outputMapper;
        List<Character> largest;

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
        mapper = new SimulinkSULMapper(inputMapper, largest, outputMapper, new SignalMapper(sigMap));

        try {
            verifier = new SimulinkVerifier(initScript, paramNames, signalStep, properties, mapper);
            verifier.setSimulationStep(0.0001);
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
    @Disabled
    void runZHA19_AFC1() {
        // Try AFC1 in ZHA19 (https://arxiv.org/pdf/1905.07549.pdf)
        // Construct the mapper
        List<Map<Character, Double>> inputMapper;
        List<Map<Character, Double>> outputMapper;
        List<Character> largest;

        {
    /*
       The range should be as follows.
	  - Pedal_Angle: [8.8 90.0]
      - Engine_Speed: [900.0 1100.0]
     */
            Map<Character, Double> pedalAngleMapper = new HashMap<>();
            pedalAngleMapper.put('a', 10.0);
            pedalAngleMapper.put('b', 20.0);
            pedalAngleMapper.put('c', 30.0);
            pedalAngleMapper.put('d', 40.0);
            pedalAngleMapper.put('e', 50.0);
            pedalAngleMapper.put('f', 60.0);
            pedalAngleMapper.put('g', 70.0);
            pedalAngleMapper.put('h', 80.0);
            pedalAngleMapper.put('i', 90.0);

            Map<Character, Double> engineSpeedMapper = new HashMap<>();
            engineSpeedMapper.put('a', 900.0);
            engineSpeedMapper.put('b', 920.0);
            engineSpeedMapper.put('c', 940.0);
            engineSpeedMapper.put('d', 960.0);
            engineSpeedMapper.put('e', 980.0);
            engineSpeedMapper.put('f', 1000.0);
            engineSpeedMapper.put('g', 1020.0);
            engineSpeedMapper.put('h', 1040.0);
            engineSpeedMapper.put('i', 1060.0);
            engineSpeedMapper.put('j', 1080.0);
            engineSpeedMapper.put('k', 1100.0);
            inputMapper = new ArrayList<>(Arrays.asList(pedalAngleMapper, engineSpeedMapper));
        }
        Function<List<Double>, Double> mu = a -> abs(a.get(0) - a.get(1)) / a.get(1);
        List<Function<List<Double>, Double>> sigMap = new ArrayList<>(Collections.singletonList(mu));
        {
            Map<Character, Double> afMapper = new HashMap<>();
            afMapper.put('a', 10.0);
            afMapper.put('b', 12.0);
            afMapper.put('c', 14.0);
            afMapper.put('d', 16.0);
            afMapper.put('e', 18.0);
            afMapper.put('f', 20.0);
            afMapper.put('g', 22.0);
            afMapper.put('h', 24.0);
            afMapper.put('i', 26.0);
            afMapper.put('j', 28.0);
            afMapper.put('k', 30.0);
            afMapper.put('l', 32.0);
            afMapper.put('m', 34.0);
            afMapper.put('n', 36.0);
            afMapper.put('o', 38.0);
            Map<Character, Double> afRefMapper = new HashMap<>();
            // mapper for the controller_mode
            Map<Character, Double> cmMapper = new HashMap<>();
            cmMapper.put('0', 0.0);

            // mapper for mu
            Map<Character, Double> muMapper = new HashMap<>();
            muMapper.put('l', 0.16);

            outputMapper = new ArrayList<>(Arrays.asList(afMapper, afRefMapper, cmMapper, muMapper));
            largest = new ArrayList<>(Arrays.asList('x', '0', '1', 'h'));
        }
        mapper = new SimulinkSULMapper(inputMapper, largest, outputMapper, new SignalMapper(sigMap));

        try {
            verifier = new SimulinkVerifier(initScript, paramNames, signalStep, propertyZHA19_AFC1, mapper);
        } catch (Exception e) {
            System.out.println(e.getMessage());
            assert false;
        }
        assertFalse(verifier.run());
        System.out.println(verifier.getCexAbstractInput());
    }

    @Test
    @Disabled
    void runHAF14_AT4() {
        // Try AT4 in HAF14 (https://easychair.org/publications/open/4bfq)
        // Construct the mapper
        List<Map<Character, Double>> inputMapper;
        List<Map<Character, Double>> outputMapper;
        List<Character> largest;

        {
    /*
       The range should be as follows.
	  - Pedal_Angle: [8.8 90.0]
      - Engine_Speed: [900.0 1100.0]
     */
            Map<Character, Double> pedalAngleMapper = new HashMap<>();
            pedalAngleMapper.put('a', 10.0);
            pedalAngleMapper.put('b', 20.0);
            pedalAngleMapper.put('c', 30.0);
            pedalAngleMapper.put('d', 40.0);
            pedalAngleMapper.put('e', 50.0);
            pedalAngleMapper.put('f', 60.0);
            pedalAngleMapper.put('g', 70.0);
            pedalAngleMapper.put('h', 80.0);
            pedalAngleMapper.put('i', 90.0);

            Map<Character, Double> engineSpeedMapper = new HashMap<>();
            engineSpeedMapper.put('a', 900.0);
            engineSpeedMapper.put('b', 920.0);
            engineSpeedMapper.put('c', 940.0);
            engineSpeedMapper.put('d', 960.0);
            engineSpeedMapper.put('e', 980.0);
            engineSpeedMapper.put('f', 1000.0);
            engineSpeedMapper.put('g', 1020.0);
            engineSpeedMapper.put('h', 1040.0);
            engineSpeedMapper.put('i', 1060.0);
            engineSpeedMapper.put('j', 1080.0);
            engineSpeedMapper.put('k', 1100.0);
            inputMapper = new ArrayList<>(Arrays.asList(pedalAngleMapper, engineSpeedMapper));
        }
        Function<List<Double>, Double> mu = a -> abs(a.get(0) - a.get(1)) / a.get(1);
        List<Function<List<Double>, Double>> sigMap = new ArrayList<>(Collections.singletonList(mu));
        {
            Map<Character, Double> afMapper = new HashMap<>();
            afMapper.put('a', 10.0);
            afMapper.put('b', 12.0);
            afMapper.put('c', 14.0);
            afMapper.put('d', 16.0);
            afMapper.put('e', 18.0);
            afMapper.put('f', 20.0);
            afMapper.put('g', 22.0);
            afMapper.put('h', 24.0);
            afMapper.put('i', 26.0);
            afMapper.put('j', 28.0);
            afMapper.put('k', 30.0);
            afMapper.put('l', 32.0);
            afMapper.put('m', 34.0);
            afMapper.put('n', 36.0);
            afMapper.put('o', 38.0);
            Map<Character, Double> afRefMapper = new HashMap<>();
            // mapper for the controller_mode
            Map<Character, Double> cmMapper = new HashMap<>();
            cmMapper.put('0', 0.0);

            // mapper for mu
            Map<Character, Double> muMapper = new HashMap<>();
            muMapper.put('l', 0.16);

            outputMapper = new ArrayList<>(Arrays.asList(afMapper, afRefMapper, cmMapper, muMapper));
            largest = new ArrayList<>(Arrays.asList('x', '0', '1', 'h'));
        }
        mapper = new SimulinkSULMapper(inputMapper, largest, outputMapper, new SignalMapper(sigMap));

        try {
            verifier = new SimulinkVerifier(initScript, paramNames, signalStep, propertyZHA19_AFC1, mapper);
        } catch (Exception e) {
            System.out.println(e.getMessage());
            assert false;
        }
        assertFalse(verifier.run());
        System.out.println(verifier.getCexAbstractInput());
    }

    @Test
    void getCexProperty() {
        assertFalse(verifier.run());
        List<String> expected = Collections.singletonList("[] (output == \"a00\")");
        assertEquals(expected, verifier.getCexProperty());
    }

    @Test
    void getCexInput() {
    }

    @Test
    void getCexOutput() {
    }
}