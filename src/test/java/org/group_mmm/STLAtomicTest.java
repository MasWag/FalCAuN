package org.group_mmm;

import net.automatalib.words.Word;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.assertEquals;

class STLAtomicTest {

    @Test
    void applyEmpty() {
        Word<ArrayList<Double>> signal = Word.epsilon();
        STLCost formula = new STLAtomic(0, STLAtomic.Operation.lt, 10);
        double expected = Double.POSITIVE_INFINITY;
        double actual = formula.apply(signal);

        assertEquals(expected, actual);
    }
}