package net.maswag.falcaun.parser;

import net.automatalib.word.Word;
import net.maswag.falcaun.IODiscreteSignal;
import net.maswag.falcaun.IOSignal;
import net.maswag.falcaun.parser.STLOutputAtomic;
import net.maswag.falcaun.parser.TemporalEventually.STLEventually;
import net.maswag.falcaun.parser.TemporalGlobally.STLGlobally;
import net.maswag.falcaun.parser.TemporalLogic.STLCost;
import net.maswag.falcaun.parser.TemporalSub.STLSub;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

class STLSubTest {
    private IOSignal<List<Double>> signal;

    @BeforeEach
    void setUp() {
        signal = new IODiscreteSignal<>(Word.epsilon(), Word.epsilon());
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
        STLCost fml = new STLSub(new STLGlobally(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 10.0)), 1, 3);
        double expect = Double.POSITIVE_INFINITY;
        double actual = fml.apply(signal);
        assertEquals(expect, actual);
    }

    @Test
    void testEventuallyToString() {
        STLCost fml = new STLSub(new STLEventually(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 10.0)), 1, 3);
        String expect = " <>_[1, 3] ( output(0) > 10.000000 )";
        String actual = fml.toString();
        assertEquals(expect, actual);
    }

    @Test
    void testGloballyToString() {
        STLCost fml = new STLSub(new STLGlobally(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 10.0)), 1, 3);
        String expect = " []_[1, 3] ( output(0) > 10.000000 )";
        String actual = fml.toString();
        assertEquals(expect, actual);
    }
}
