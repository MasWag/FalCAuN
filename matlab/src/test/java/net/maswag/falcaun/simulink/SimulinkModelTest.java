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
import java.util.ArrayList;
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

    @Nested
    class AFC {
        private final String initScript = "cd " + PWD + "/src/test/resources/MATLAB; initAFC;";

        @BeforeEach
        void setUp() throws ExecutionException, InterruptedException {
            SimulinkModel.clearSimulinkBuildArtifacts(MATLAB_RESOURCES);
            mdl = createModel();
        }

        private SimulinkModel createModel() throws ExecutionException, InterruptedException {
            SimulinkModel model = new SimulinkModel(initScript,
                    Arrays.asList("Pedal Angle", "Engine Speed"),
                    signalStep, 0.0025);
            model.setSimulationStep(0.0001);
            return model;
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
        void step() throws ExecutionException, InterruptedException {
            final double eps = 1.0e-9;
            final double outputEps = 1.0e-2;
            // Give [80.0, 900.0] multiple times.
            List<Double> input = Arrays.asList(80.0, 900.0);
            List<List<Double>> fullInput = new ArrayList<>();
            List<Double> finalTimes = new ArrayList<>();
            List<List<Double>> finalStepValues = new ArrayList<>();
            for (int i = 0; i < 4; i++) {
                fullInput.add(input);
                ValueWithTime<List<Double>> result = mdl.step(input);
                List<Double> timestamps = result.getTimestamps();
                Assertions.assertFalse(timestamps.isEmpty());
                // The current fast low-level strategy replays the accumulated prefix from the initial state.
                Assertions.assertEquals(0.0, timestamps.get(0), eps);
                double currentLastTime = timestamps.get(timestamps.size() - 1);
                if (i == 0) {
                    Assertions.assertEquals(1, timestamps.size());
                }
                Assertions.assertEquals(signalStep * i, currentLastTime, eps);
                finalTimes.add(currentLastTime);
                finalStepValues.add(result.getValues().get(result.getValues().size() - 1));
            }

            mdl.close();
            mdl = createModel();
            for (int i = 0; i < fullInput.size(); i++) {
                ValueWithTime<List<Double>> executeResult = mdl.execute(Word.fromList(fullInput.subList(0, i + 1)));
                assertOutputClose(executeResult.at(finalTimes.get(i)), finalStepValues.get(i), outputEps);
            }
            // Since the total number of steps is 4, the last time stamp should be 6.0
            Assertions.assertEquals(signalStep * 3, finalTimes.get(finalTimes.size() - 1), eps);
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

    private static void assertOutputClose(List<Double> expected, List<Double> actual, double eps) {
        Assertions.assertEquals(expected.size(), actual.size());
        for (int i = 0; i < expected.size(); i++) {
            Assertions.assertEquals(expected.get(i), actual.get(i), eps);
        }
    }
}
