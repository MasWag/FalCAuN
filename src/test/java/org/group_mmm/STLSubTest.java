package org.group_mmm;

import net.automatalib.words.Word;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;

import static org.junit.jupiter.api.Assertions.assertEquals;

class STLSubTest {
    private Word<ArrayList<Double>> signal;

    @BeforeEach
    void setUp() {
        signal = Word.epsilon();
    }

    @Test
    void applyShortEventual() {
        STLCost fml = new STLSub(new STLEventually(new STLAtomic(0, false, 10.0)), 1, 3);
        double expect = Double.NEGATIVE_INFINITY;
        double actual = fml.apply(signal);
        assertEquals(expect, actual);
    }

    @Test
    void applyShortGlobal() {
        STLCost fml = new STLSub(new STLGlobal(new STLAtomic(0, false, 10.0)), 1, 3);
        double expect = Double.POSITIVE_INFINITY;
        double actual = fml.apply(signal);
        assertEquals(expect, actual);
    }
}