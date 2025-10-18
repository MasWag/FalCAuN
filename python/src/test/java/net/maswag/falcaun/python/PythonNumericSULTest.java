package net.maswag.falcaun.python;

import org.junit.jupiter.api.Test;

import net.maswag.falcaun.IOSignal;
import net.maswag.falcaun.IOSignalPiece;
import net.maswag.falcaun.python.PythonNumericSUL;

import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertIterableEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertEquals;


class PythonNumericSULTest {
    // test-numeric-sul.py accumulates the sum of the input List<Double> and returns it.
    // The first output is truncated to 100.0 if it exceeds 100.0.
    // The second output is the sum modulo 100.0.
    static final String numericScript = "./src/test/resources/test_numeric_sul.py";
    static final String numericScriptWithExec = "./src/test/resources/test_numeric_sul_with_exec.py";

    @Test
    void numericStepTest() throws Exception {
        try (var sul = new PythonNumericSUL(numericScript)) {
            sul.pre();

            var input1 = Arrays.asList(1.0, 2.0);
            var piece1 = sul.step(input1);
            assertNotNull(piece1);
            var output1 = piece1.getOutputSignal();
            assertIterableEquals(Arrays.asList(3.0, 3.0), output1);

            var input2 = Arrays.asList(2.0, 3.0);
            var piece2 = sul.step(input2);
            assertNotNull(piece2);
            var output2 = piece2.getOutputSignal();
            assertIterableEquals(Arrays.asList(8.0, 8.0), output2);

            sul.post();
            assertFalse(sul.canFork());
            assertThrows(UnsupportedOperationException.class, sul::fork);
        }
    }

    @Test
    void numericExecuteTest() throws Exception {
        try (var sul = new PythonNumericSUL(numericScript)) {
            sul.pre();

            var inputSeq = java.util.List.of(
                java.util.Arrays.asList(10.0, 0.5),
                java.util.Arrays.asList(20.0, 0.5),
                java.util.Arrays.asList(50.0, 0.5),
                java.util.Arrays.asList(80.0, 0.5),
                java.util.Arrays.asList(-20.0, 0.5)
            );
            var word = net.automatalib.word.Word.fromList(inputSeq);
            var ioSignal = sul.execute(word);
            var outputs = ioSignal.getOutputSignal();
            assertEquals(5, outputs.size());
            assertIterableEquals(java.util.Arrays.asList(10.5, 10.5), outputs.getSymbol(0));
            assertIterableEquals(java.util.Arrays.asList(31.0, 31.0), outputs.getSymbol(1));
            assertIterableEquals(java.util.Arrays.asList(81.5, 81.5), outputs.getSymbol(2));
            assertIterableEquals(java.util.Arrays.asList(100.0, 62.0), outputs.getSymbol(3));
            assertIterableEquals(java.util.Arrays.asList(80.5, 42.5), outputs.getSymbol(4));

            sul.post();
        }
    }

    @Test
    void numericExecuteTest2() throws Exception {
        // Same results as numericExecuteTest, but using exec function in python.
        try (var sul = new PythonNumericSUL(numericScriptWithExec)) {
            sul.pre();

            var inputSeq = java.util.List.of(
                java.util.Arrays.asList(10.0, 0.5),
                java.util.Arrays.asList(20.0, 0.5),
                java.util.Arrays.asList(50.0, 0.5),
                java.util.Arrays.asList(80.0, 0.5),
                java.util.Arrays.asList(-20.0, 0.5)
            );
            var word = net.automatalib.word.Word.fromList(inputSeq);
            var ioSignal = sul.execute(word);
            var outputs = ioSignal.getOutputSignal();
            assertEquals(5, outputs.size());
            assertIterableEquals(java.util.Arrays.asList(10.5, 10.5), outputs.getSymbol(0));
            assertIterableEquals(java.util.Arrays.asList(31.0, 31.0), outputs.getSymbol(1));
            assertIterableEquals(java.util.Arrays.asList(81.5, 81.5), outputs.getSymbol(2));
            assertIterableEquals(java.util.Arrays.asList(100.0, 62.0), outputs.getSymbol(3));
            assertIterableEquals(java.util.Arrays.asList(80.5, 42.5), outputs.getSymbol(4));

            sul.post();
        }
    }
}
