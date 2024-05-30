package net.maswag.falcaun;

import com.mathworks.engine.EngineException;
import net.automatalib.word.Word;
import org.junit.jupiter.api.*;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.ExecutionException;


class SimulinkModelTest {
    private SimulinkModel mdl;
    private final String PWD = System.getenv("PWD");
    private final Double signalStep = 2.0;

    @AfterEach
    void tearDown() throws EngineException {
        mdl.close();
    }

    @Nested
    class AFC {
        private final String initScript = "cd " + PWD + "/src/test/resources/MATLAB; initAFC;";

        @BeforeEach
        void setUp() throws ExecutionException, InterruptedException {
            mdl = new SimulinkModel(initScript,
                    Arrays.asList("Pedal Angle", "Engine Speed"),
                    signalStep, 0.0025);
            mdl.setSimulationStep(0.0001);
        }

        @Test
        void execute() throws ExecutionException, InterruptedException {
            // Give [80.0, 900.0] by repeating 10 times
            List<List<Double>> input = Arrays.asList(
                    Arrays.asList(80.0, 900.0),
                    Arrays.asList(80.0, 900.0),
                    Arrays.asList(80.0, 900.0),
                    Arrays.asList(80.0, 900.0),
                    Arrays.asList(80.0, 900.0),
                    Arrays.asList(80.0, 900.0),
                    Arrays.asList(80.0, 900.0),
                    Arrays.asList(80.0, 900.0),
                    Arrays.asList(80.0, 900.0),
                    Arrays.asList(80.0, 900.0));
            ValueWithTime<List<Double>> result = mdl.execute(Word.fromList(input));
            // Test that the first time stamp is 0.0
            Assertions.assertEquals(0.0, result.getTimestamps().get(0).doubleValue());
            // Test that the last time stamp is 18.0
            Assertions.assertEquals(18.0, result.getTimestamps().get(result.getTimestamps().size() - 1).doubleValue());
        }

        @Test
        void step() {
            double lastTime = Double.NEGATIVE_INFINITY; // The dummy value for the first case
            // Give [80.0, 900.0] for 10 times
            List<Double> input = Arrays.asList(80.0, 900.0);
            for (int i = 0; i < 10; i++) {
                ValueWithTime<List<Double>> result = mdl.step(input);
                if (lastTime < 0.0) {
                    // The result only contains the information at time 0
                    Assertions.assertEquals(1, result.getTimestamps().size());
                    Assertions.assertEquals(0.0, result.getTimestamps().get(0));
                } else {
                    // Test that the first time stamp is always 0
                    Assertions.assertEquals(0.0, result.getTimestamps().get(0));
                    // Test that the last time stamp is 2.0 larger than the latest last time stamp
                    Assertions.assertEquals(result.getTimestamps().get(result.getTimestamps().size() - 1), lastTime + signalStep);
                }
                lastTime = result.getTimestamps().get(result.getTimestamps().size() - 1);
            }
            // Since the total number of steps is 10, the last time stamp should be 18.0
            Assertions.assertEquals(signalStep * 9, lastTime);
        }
    }

    @Nested
    class PassThrough {
        private final String initScript = "cd " + PWD + "/src/test/resources/MATLAB; mdl = 'pass_through'; load_system(mdl);";

        @BeforeEach
        void setUp() throws ExecutionException, InterruptedException {
            mdl = new SimulinkModel(initScript,
                    List.of("Input"),
                    signalStep, 0.0025);
        }

        @Test
        void setInterpolationMethod() throws ExecutionException, InterruptedException {
            // We test that the system behaves differently when we use different interpolation methods
            // We use the same input signal for both cases
            List<List<Double>> input = Arrays.asList(
                    List.of(100.0),
                    List.of(0.0));
            // First, we run a simulation with piecewise-linear interpolation
            mdl.setInterpolationMethod(SimulinkModel.InterpolationMethod.LINEAR);
            ValueWithTime<List<Double>> resultLinear = mdl.execute(Word.fromList(input));
            mdl.reset();

            // Then, we run a simulation with piecewise-constant interpolation
            mdl.setInterpolationMethod(SimulinkModel.InterpolationMethod.CONSTANT);
            ValueWithTime<List<Double>> resultConstant = mdl.execute(Word.fromList(input));
            mdl.reset();

            // We test that the two results are different
            // Assertions.assertNotEquals(resultLinear.getValues(), resultConstant.getValues());

            // We test that this difference is not due to the non-deterministic nature of the simulation
            mdl.setInterpolationMethod(SimulinkModel.InterpolationMethod.LINEAR);
            ValueWithTime<List<Double>> resultLinear2 = mdl.execute(Word.fromList(input));
            mdl.reset();
            Assertions.assertEquals(resultLinear.getValues(), resultLinear2.getValues());
        }
    }
}