package net.maswag.falcaun;

import net.automatalib.word.Word;
import org.junit.jupiter.api.*;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.ExecutionException;


class PythonModelTest {
    private PythonModel mdl;
    private final String PWD = System.getenv("PWD");
    private final Double signalStep = 2.0;

    @AfterEach
    void tearDown() {
        mdl.close();
    }

    @Nested
    class AFC {
        private final String initScript = "cd " + PWD + "/src/test/resources/MATLAB; initAFC;";

        @BeforeEach
        void setUp() throws ExecutionException, InterruptedException {
            mdl = new PythonModel(initScript, signalStep);
        }

        @Test
        void execute() throws ExecutionException, InterruptedException, Exception {
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
        void step() throws Exception {
            /* double lastTime = Double.NEGATIVE_INFINITY; // The dummy value for the first case
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
            Assertions.assertEquals(signalStep * 9, lastTime); */
        }
    }

    @Nested
    class PassThrough {
        private final String initScript = "cd " + PWD + "/src/test/resources/MATLAB; mdl = 'pass_through'; load_system(mdl);";

        @BeforeEach
        void setUp() throws ExecutionException, InterruptedException {
            mdl = new PythonModel(initScript, signalStep);
        }
    }
}