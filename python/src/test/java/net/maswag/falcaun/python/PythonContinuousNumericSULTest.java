package net.maswag.falcaun.python;

import org.junit.jupiter.api.Test;

import lombok.extern.slf4j.Slf4j;

import java.util.Arrays;
import java.util.List;
import java.util.ArrayList;
import net.automatalib.word.Word;
import net.maswag.falcaun.ExtendedIOSignalPiece;
import net.maswag.falcaun.IOContinuousSignal;
import net.maswag.falcaun.python.PythonContinuousNumericSUL;

import static org.junit.jupiter.api.Assertions.*;

@Slf4j
class PythonContinuousNumericSULTest {
    static final String script = "./src/test/resources/test_continuous_numeric_sul.py";
    static final Double EPS = 1e-8;
    @Test
    void stepTest() throws Exception {
        try (var sul = new PythonContinuousNumericSUL(script, 1.0)) {
            sul.pre();

            var input1 = Arrays.asList(0.0); // acc=0.0
            @SuppressWarnings("unused")
            var piece1 = sul.step(input1);

            var input2 = Arrays.asList(0.0);
            var piece2 = sul.step(input2);
            assertNotNull(piece2, "piece2 should not be null");
            var values2 = piece2.getOutputSignal();
            assertEquals(0.0, values2.get(0), EPS);

            var input3 = Arrays.asList(1.0);
            var piece3 = sul.step(input3);
            var values3 = piece3.getOutputSignal();
            assertEquals(0.859375, values3.get(0), EPS);

            sul.post();
        }
    }

    @Test
    void execTest() throws Exception {
        try (var sul = new PythonContinuousNumericSUL(script, 1.0)) {
            sul.pre();
            var inputSeq = Arrays.asList(
                Arrays.asList(0.0),
                Arrays.asList(0.125),
                Arrays.asList(1.0)
            );
            var word = Word.fromList(inputSeq);
            var ioSignal = sul.execute(word);
            var allValues = new ArrayList<List<Double>>();
            ioSignal.stream().forEach(piece ->
                allValues.addAll(((ExtendedIOSignalPiece<List<Double>>) piece).getPreviousOutputSignals())
            );
            assertEquals(0.0, allValues.get(8).get(0), EPS);
            assertEquals(0.859375, allValues.get(16).get(0), EPS);
        }
    }
}
