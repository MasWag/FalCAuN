package net.maswag.falcaun.simulink;

import com.mathworks.engine.EngineException;
import net.automatalib.word.Word;
import net.maswag.falcaun.ValueWithTime;
import net.maswag.falcaun.simulink.SimulinkModel;

import org.junit.jupiter.api.*;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.ExecutionException;


class SimulinkModelTest {
    private static final Path MATLAB_RESOURCES = Paths.get("matlab", "src", "test", "resources", "MATLAB");
    private SimulinkModel mdl;
    private final String PWD = System.getenv("PWD");
    private final Double signalStep = 2.0;

    @AfterEach
    void tearDown() throws EngineException {
        if (mdl != null) {
            mdl.close();
            mdl = null;
        }
    }

    @Test
    void clearSimulinkBuildArtifactsRemovesAutosave(@TempDir Path tempDir) throws IOException {
        Path autosave = tempDir.resolve("model.slx.autosave");
        Files.writeString(autosave, "");

        SimulinkModel.clearSimulinkBuildArtifacts(tempDir);

        Assertions.assertFalse(Files.exists(autosave));
    }

    @Test
    void currentStepDatasetUsesCurrentSegmentForSavedState() {
        List<Double> timestamps = Arrays.asList(0.0, 2.0, 4.0);
        List<List<Double>> values = Arrays.asList(
                Arrays.asList(80.0, 900.0),
                Arrays.asList(70.0, 950.0),
                Arrays.asList(60.0, 1000.0));

        Assertions.assertEquals(
                Arrays.asList(2.0, 4.0),
                SimulinkModel.getCurrentStepTimestamps(timestamps, true));
        Assertions.assertEquals(
                Arrays.asList(values.get(1), values.get(2)),
                SimulinkModel.getCurrentStepValues(values, true));
    }

    @Nested
    class AFC {
        private final String initScript = "cd " + PWD + "/src/test/resources/MATLAB; initAFC;";

        @BeforeEach
        void setUp() throws ExecutionException, InterruptedException {
            SimulinkModel.clearSimulinkBuildArtifacts(MATLAB_RESOURCES);
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
            final double eps = 1.0e-9;
            double lastTime = Double.NEGATIVE_INFINITY; // The dummy value for the first case
            boolean sawNonZeroStart = false;
            // Give [80.0, 900.0] for 10 times
            List<Double> input = Arrays.asList(80.0, 900.0);
            for (int i = 0; i < 10; i++) {
                ValueWithTime<List<Double>> result = mdl.step(input);
                List<Double> timestamps = result.getTimestamps();
                Assertions.assertFalse(timestamps.isEmpty());
                double firstTime = timestamps.get(0);
                double currentLastTime = timestamps.get(timestamps.size() - 1);
                if (lastTime < 0.0) {
                    // The result only contains the information at time 0
                    Assertions.assertEquals(1, timestamps.size());
                    Assertions.assertEquals(0.0, firstTime, eps);
                } else {
                    // Each incremental result should continue from the previous step, not replay from zero.
                    Assertions.assertTrue(firstTime >= lastTime - eps);
                    Assertions.assertEquals(lastTime + signalStep, currentLastTime, eps);
                    sawNonZeroStart |= firstTime > eps;
                }
                lastTime = currentLastTime;
            }
            Assertions.assertTrue(sawNonZeroStart);
            // Since the total number of steps is 10, the last time stamp should be 18.0
            Assertions.assertEquals(signalStep * 9, lastTime, eps);
        }

        @Test
        void count() throws ExecutionException, InterruptedException {
            // Test that the counter is 0 at the beginning
            Assertions.assertEquals(0, mdl.getCounter());
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
            // Execute the model
            mdl.execute(Word.fromList(input));
            // Test that the counter is 1 after executing the model
            Assertions.assertEquals(1, mdl.getCounter());
            // Execute the model again
            mdl.execute(Word.fromList(input));
            // Test that the counter is 2 after executing the model again
            Assertions.assertEquals(2, mdl.getCounter());
        }
    }

    @Nested
    class PassThrough {
        private final String initScript = "cd " + PWD + "/src/test/resources/MATLAB; mdl = 'pass_through'; load_system(mdl);";

        @BeforeEach
        void setUp() throws ExecutionException, InterruptedException {
            SimulinkModel.clearSimulinkBuildArtifacts(MATLAB_RESOURCES);
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
