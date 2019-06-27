package org.group_mmm;

import net.automatalib.words.Word;
import org.junit.Ignore;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ExecutionException;

import static org.junit.jupiter.api.Assertions.*;

class SimulinkSULTest {
    private SimulinkSUL sul;

    void setUp(String initScript, List<String> paramNames, double signalStep) throws Exception {
        this.sul = new SimulinkSUL(initScript, paramNames, signalStep);
    }

    @Nested
    class AFC {
        // The outputs are, AF, AFref, and mode
        int expectedOutputSize = 3;

        @BeforeEach
        void setUp() throws Exception {
            SimulinkSULTest.this.setUp(
                    "cd ./src/test/resources/MATLAB; initAFC;",
                    Arrays.asList("Pedal Angle", "Engine Speed"),
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
            List<Double> input = Arrays.asList(80.0, 900.0);
            List<Double> output = sul.step(input);
            assertNotNull(output);
            assertEquals(expectedOutputSize, output.size());

            input = Arrays.asList(85.0, 920.0);
            output = sul.step(input);
            assertNotNull(output);
            assertEquals(expectedOutputSize, output.size());
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

        @BeforeEach
        void setUp() throws Exception {
            SimulinkSULTest.this.setUp(
                    "cd ./src/test/resources/MATLAB; initAT;",
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
            List<Double> output = sul.step(input);
            assertNotNull(output);
            assertEquals(expectedOutputSize, output.size());

            input = Arrays.asList(0.0, 200.0);
            output = sul.step(input);
            assertNotNull(output);
            assertEquals(expectedOutputSize, output.size());
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
            final int times = 50;
            Word<List<Double>> input = Word.fromList(Collections.nCopies(length, Arrays.asList(100.0, 0.0)));
            assertEquals(length, input.size());

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
}