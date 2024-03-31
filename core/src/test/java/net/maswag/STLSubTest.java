package net.maswag;

import net.automatalib.word.Word;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

class STLSubTest {
    private IOSignal signal;

    @BeforeEach
    void setUp() {
        signal = new IOSignal(Word.epsilon(), Word.epsilon());
    }

    @Test
    void applyShortEventual() {
        STLCost fml = new STLSub(new STLEventually(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 10.0)), 1, 3);
        double expect = Double.POSITIVE_INFINITY;
        double actual = fml.apply(signal);
        assertEquals(expect, actual);
    }

    @Test
    void applyShortGlobal() {
        STLCost fml = new STLSub(new STLGlobal(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 10.0)), 1, 3);
        double expect = Double.POSITIVE_INFINITY;
        double actual = fml.apply(signal);
        assertEquals(expect, actual);
    }
}