package net.maswag;

import net.automatalib.word.Word;
import org.junit.Ignore;
import org.junit.jupiter.api.*;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ExecutionException;

import static org.junit.jupiter.api.Assertions.*;

class SimulinkSULTest {
    private SimulinkSUL sul;

    void setUp(String initScript, List<String> paramNames, double signalStep) throws Exception {
        this.sul = new SimulinkSUL(initScript, paramNames, signalStep, 0.0025);
    }

    @AfterEach
    void teardown() throws Throwable {
        this.sul.close();
    }

    @Nested
    class AFC {
        // The outputs are, AF, AFref, and mode
        int expectedOutputSize = 3;
        private final String PWD = System.getenv("PWD");
        private final String initScript = "cd " + PWD + "/src/test/resources/MATLAB; initAFC;";

        @BeforeEach
        void setUp() throws Exception {
            SimulinkSULTest.this.setUp(
                    initScript,
                    Arrays.asList("Pedal Angle", "Engine Speed"),
                    2.0);
            SimulinkSULTest.this.sul.setSimulationStep(0.0001);
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
            List<Double> input = Arrays.asList(80.0, 900.0);
            IOSignalPiece<List<Double>> firstPair = sul.step(input);
            assert firstPair != null;
            List<Double> firstOutput = firstPair.getOutputSignal();
            assertNotNull(firstOutput);
            assertEquals(expectedOutputSize, firstOutput.size());

            input = Arrays.asList(85.0, 920.0);
            IOSignalPiece<List<Double>> secondPair = sul.step(input);
            assert secondPair != null;
            List<Double> secondOutput = secondPair.getOutputSignal();
            assertNotNull(secondOutput);
            assertEquals(expectedOutputSize, secondOutput.size());
            // Since the inputs are totally different, the output should change.
            assertNotEquals(firstOutput, secondOutput);
        }

        @Test
        void fork() {
            assertThrows(UnsupportedOperationException.class, () -> sul.fork());
        }
    }

    @Nested
    class AT {
        // The outputs are, velocity, rotation, and gear
        int expectedOutputSize = 3;
        private final String PWD = System.getenv("PWD");
        private final String initScript = "cd " + PWD + "/src/test/resources/MATLAB; initAT;";

        @BeforeEach
        void setUp() throws Exception {
            SimulinkSULTest.this.setUp(
                    initScript,
                    Arrays.asList("throttle", "brake"),
                    2.0);
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
            List<Double> input = Arrays.asList(80.0, 0.0);
            IOSignalPiece<List<Double>> firstPair = sul.step(input);
            assert firstPair != null;
            List<Double> firstOutput = firstPair.getOutputSignal();
            assertNotNull(firstOutput);
            assertEquals(expectedOutputSize, firstOutput.size());

            input = Arrays.asList(0.0, 200.0);
            IOSignalPiece<List<Double>> secondPair = sul.step(input);
            assert secondPair != null;
            List<Double> secondOutput = secondPair.getOutputSignal();
            assertNotNull(secondOutput);
            assertEquals(expectedOutputSize, secondOutput.size());
            // Since the inputs are totally different, the output should change.
            assertNotEquals(firstOutput, secondOutput);
        }

        @Test
        void execute() throws InterruptedException, ExecutionException {
            final int length = 15;
            Word<List<Double>> input = Word.fromList(Collections.nCopies(length, Arrays.asList(100.0, 0.0)));
            assertEquals(length, input.size());
            Word<List<Double>> output = sul.execute(input);
            assertNotNull(output);
            assertEquals(length, output.size());
        }

        @Ignore
        @Test
        void executeMeasure() throws InterruptedException, ExecutionException {
            final int length = 15;
            final int times = 200;
            Word<List<Double>> input = Word.fromList(Collections.nCopies(length, Arrays.asList(100.0, 0.0)));
            assertEquals(length, input.size());
            // Execute it once before the measurement to remove the potential overhead at the initial execution.
            sul.execute(input);

            long startTime = System.nanoTime();
            for (int i = 0; i < times; i++) {
                sul.execute(input);
            }
            long endTime = System.nanoTime();
            System.out.println("Average Execution Time of SimulinkSUL::execute: " + ((endTime - startTime) / (times * 1000000000.0)) + " [sec]");
        }


        @Test
        void fork() {
            assertThrows(UnsupportedOperationException.class, () -> sul.fork());
        }
    }

    @Nested
    @Disabled // SC benchmark requires Deep Learning toolkit of MATLAB.
    class SC {
        private final String PWD = System.getenv("PWD");
        private final String initScript = "cd " + PWD + "/src/test/resources/MATLAB; mdl = 'steamcondense_RNN_22'; load_system(mdl)";
        // The outputs are, AF, AFref, and mode
        int expectedOutputSize = 3;

        @BeforeEach
        void setUp() throws Exception {
            SimulinkSULTest.this.setUp(
                    initScript,
                    Arrays.asList("Pedal Angle", "Engine Speed"),
                    2.0);
            SimulinkSULTest.this.sul.setSimulationStep(0.0001);
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
            List<Double> input = Arrays.asList(80.0, 0.0);
            IOSignalPiece<List<Double>> firstPair = sul.step(input);
            assert firstPair != null;
            List<Double> firstOutput = firstPair.getOutputSignal();
            assertNotNull(firstOutput);
            assertEquals(expectedOutputSize, firstOutput.size());

            input = Arrays.asList(0.0, 200.0);
            IOSignalPiece<List<Double>> secondPair =  sul.step(input);
            assert secondPair != null;
            List<Double> secondOutput = secondPair.getOutputSignal();
            assertNotNull(secondOutput);
            assertEquals(expectedOutputSize, secondOutput.size());
            // Since the inputs are totally different, the output should change.
            assertNotEquals(firstOutput, secondOutput);
        }

        @Test
        void execute() throws InterruptedException, ExecutionException {
            final int length = 15;
            Word<List<Double>> input = Word.fromList(Collections.nCopies(length, Arrays.asList(100.0, 0.0)));
            assertEquals(length, input.size());
            Word<List<Double>> output = sul.execute(input);
            assertNotNull(output);
            assertEquals(length, output.size());
        }
    }
}