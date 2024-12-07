package net.maswag.falcaun;

import org.junit.jupiter.api.*;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

import static java.lang.Math.abs;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.containsInAnyOrder;
import static org.hamcrest.Matchers.greaterThan;
import static org.junit.jupiter.api.Assertions.*;

class SimulinkSULVerifierTest {
    private final String PWD = System.getenv("PWD");
    private String initScript;
    /*
       The range should be as follows.
	  - Pedal_Angle: [8.8 90.0]
      - Engine_Speed: [900.0 1100.0]
     */
    private final List<String> paramNames = Arrays.asList("Pedal Angle", "Engine Speed");
    private Double signalStep = 10.0;
    private PythonSULVerifier verifier;
    private AdaptiveSTLUpdater<List<Double>> properties;
    private NumericSULMapper mapper;
    private final List<Function<IOSignalPiece<List<Double>>, Double>> sigMap = Collections.emptyList();
    private final AdaptiveSTLUpdater<List<Double>> propertyZHA19_AFC1 = new StopDisprovedEQOracle.StaticLTLList<>(Collections.singletonList("X [] (output == \"a00l\" || output == \"a01l\" || output == \"a01h\" || output == \"b00l\" || output == \"b01l\" || output == \"b01h\" || output == \"b00l\" || output == \"b01l\" || output == \"b01h\"|| output == \"c00l\" || output == \"c01l\" || output == \"c01h\")"));
    STLFactory factory = new STLFactory();

    @BeforeEach
    void setUp() {
        initScript = "cd " + PWD + "/src/test/resources/MATLAB; initAFC;";
        signalStep = 10.0;
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
        mapper = new NumericSULMapper(inputMapper, largest, outputMapper, new SimpleSignalMapper(sigMap));
        // [] (velocity < 10)
        properties = new StaticSTLList<>(Collections.singletonList(
                factory.parse("[] (signal(0) < 10.0)", inputMapper, outputMapper, largest)));

        try {
            verifier = new PythonSULVerifier(initScript, signalStep, properties, mapper);
            verifier.addWpMethodEQOracle(1);
        } catch (Exception e) {
            System.out.println(e.getMessage());
            assert false;
        }
    }

    @AfterEach
    void tearDown() throws Exception {
        this.verifier.close();
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
        Function<IOSignalPiece<List<Double>>, Double> mu = a -> abs(a.getOutputSignal().get(0) -
                a.getOutputSignal().get(1)) / a.getOutputSignal().get(1);
        List<Function<IOSignalPiece<List<Double>>, Double>> sigMap = new ArrayList<>(Collections.singletonList(mu));
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
        mapper = new NumericSULMapper(inputMapper, largest, outputMapper, new SimpleSignalMapper(sigMap));

        try {
            verifier = new PythonSULVerifier(initScript, signalStep, propertyZHA19_AFC1, mapper);
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
        Function<IOSignalPiece<List<Double>>, Double> mu =
                a -> abs(a.getOutputSignal().get(0) - a.getOutputSignal().get(1)) / a.getOutputSignal().get(1);
        List<Function<IOSignalPiece<List<Double>>, Double>> sigMap = new ArrayList<>(Collections.singletonList(mu));
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
        mapper = new NumericSULMapper(inputMapper, largest, outputMapper, new SimpleSignalMapper(sigMap));

        try {
            verifier = new PythonSULVerifier(initScript, signalStep, propertyZHA19_AFC1, mapper);
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
        List<TemporalLogic<List<Double>>> expected = properties.getSTLProperties();
        assertEquals(expected, verifier.getCexProperty());
    }

    @Test
    @Disabled
    void getCexInput() {
    }

    @Test
    @Disabled
    void getCexOutput() {
    }

    @Nested
    class AutoTransTest {
        List<Map<Character, Double>> inputMapper;
        List<Map<Character, Double>> outputMapper;
        List<Character> largest;

        @BeforeEach
        void setUp() {
            initScript = "cd " + PWD + "/src/test/resources/MATLAB; initAT;";
            signalStep = 2.0;

            // Construct the mapper
            {
                Map<Character, Double> mapper1 = new HashMap<>();
                mapper1.put('a', 00.0);
                mapper1.put('b', 100.0);
                Map<Character, Double> mapper2 = new HashMap<>();
                mapper2.put('a', 0.0);
                mapper2.put('b', 325.0);
                inputMapper = new ArrayList<>(Arrays.asList(mapper1, mapper2));
            }
            {
                Map<Character, Double> mapper1 = new HashMap<>();
                mapper1.put('a', 120.0);
                Map<Character, Double> mapper2 = new HashMap<>();
                mapper2.put('a', 4750.0);
                mapper2.put('b', 6000.0);
                Map<Character, Double> mapper3 = new HashMap<>();

                outputMapper = new ArrayList<>(Arrays.asList(mapper1, mapper2, mapper3));
                largest = new ArrayList<>(Arrays.asList('b', 'c', 'a'));
            }
            mapper = new NumericSULMapper(inputMapper, largest, outputMapper, new SimpleSignalMapper(sigMap));
        }

        @Test
        void setTimeout() throws Exception {
            // generate properties
            String stlString = "alw_[0, 3] (signal(1) < 6000)";
            TemporalLogic.STLCost stl = factory.parse(stlString, inputMapper, outputMapper, largest);
            properties = new StaticSTLList<>(Collections.singletonList(stl));
            // define the verifier
            verifier = new PythonSULVerifier(initScript, signalStep, properties, mapper);
            // set timeout
            long timeout = 2 * 60;
            verifier.setTimeout(timeout);
            // add equivalence oracle
            verifier.addGAEQOracleAll(25, 1000, ArgParser.GASelectionKind.Tournament,
                    50, 0.9, 0.01);
            long startTime = System.nanoTime();
            assertTrue(verifier.run());
            long duration = (System.nanoTime() - startTime) / 1000 / 1000 / 1000;
            assertThat("Execution time", duration, greaterThan(timeout));
        }

        @Nested
        class AT1Test {
            TemporalLogic.STLCost stl;

            @BeforeEach
            void setUp() {
                String stlString = "alw_[0, 20] (signal(0) < 120)";
                stl = factory.parse(stlString, inputMapper, outputMapper, largest);
            }

            @Test
            void runStatic() {
                // generate properties
                properties = new StaticSTLList<>(Collections.singletonList(stl));
            }

            @Test
            void runAdaptive() {
                // generate properties
                properties = new AdaptiveSTLList<>(Collections.singletonList(stl));
            }

            @AfterEach
            void tearDown() throws Exception {
                // define the verifier
                verifier = new PythonSULVerifier(initScript, signalStep, properties, mapper);
                verifier.addGAEQOracleAll(15, 5000, ArgParser.GASelectionKind.Tournament,
                        50, 0.9, 0.01);
                assertFalse(verifier.run());
            }
        }


        @Nested
        class AT1AndAT2Test {
            List<String> expectedStlStringList;
            List<TemporalLogic.STLCost> stlList;

            @BeforeEach
            void setUp() {
                List<String> stlStringList = Arrays.asList(
                        "alw_[0, 20] (signal(0) < 120)",
                        "alw_[0, 10] (signal(1) < 4750)");
                stlList = stlStringList.stream().map(stlString ->
                        factory.parse(stlString, inputMapper, outputMapper, largest)).collect(Collectors.toList());
                expectedStlStringList = stlList.stream().map(Object::toString).collect(Collectors.toList());
            }

            @Test
            void runStatic() throws Exception {
                // generate properties
                properties = new StaticSTLList<>(stlList);
                verify();
            }

            @Test
            void runAdaptive() throws Exception {
                // generate properties
                properties = new AdaptiveSTLList<>(stlList);
                verify();
            }

            void verify() throws Exception {
                // define the verifier
                verifier = new PythonSULVerifier(initScript, signalStep, properties, mapper);
                verifier.addGAEQOracleAll(15, 5000, ArgParser.GASelectionKind.Tournament,
                        50, 0.9, 0.01);
                assertFalse(verifier.run());
                // Confirm that the number of the properties is correctly handled
                assertThat("All the given properties should be reported as counterexamples",
                        verifier.getCexProperty().stream().map(Object::toString).collect(Collectors.toList()),
                        containsInAnyOrder(expectedStlStringList.get(0), expectedStlStringList.get(1)));
                assertEquals(2, verifier.getCexProperty().size());
                // Confirm that the number of the counterexamples is correctly handled
                assertEquals(2, (int) verifier.getCexAbstractInput().stream().filter(Objects::nonNull).count());
            }
        }
    }
}
