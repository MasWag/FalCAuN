package org.group_mmm;

import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

class STLAtomicTest {

    @Test
    void applyEmpty() {
        Word<List<Double>> signal = Word.epsilon();
        STLCost formula = new STLAtomic(0, STLAtomic.Operation.lt, 10);
        double expected = Double.POSITIVE_INFINITY;
        double actual = formula.apply(signal);

        assertEquals(expected, actual);
    }

    @Test
    void ne() {
        WordBuilder<List<Double>> builder = new WordBuilder<>();
        builder.append(new ArrayList<>(Collections.singletonList(0.0)));
        Word<List<Double>> signal = builder.toWord();
        STLCost formula = new STLAtomic(0, STLAtomic.Operation.ne, 2);
        double expected = 2;
        double actual = formula.apply(signal);

        assertEquals(expected, actual);
    }
}