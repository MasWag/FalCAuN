package net.maswag.falcaun;

import net.automatalib.word.Word;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

class SignalTest {
    private Signal inputSignal;
    private List<List<Double>> rawInput;

    @BeforeEach
    void setUp() {
        this.inputSignal = new Signal(2.0);
        rawInput = new ArrayList<>();
        for (int i = 0; i < 9; i++) {
            rawInput.add(new ArrayList<>());
            rawInput.get(i).add(100.0);
            rawInput.get(i).add(0.0);
        }
        rawInput.add(new ArrayList<>());
        rawInput.get(9).add(0.0);
        rawInput.get(9).add(0.0);
    }

    @Test
    void add() {
        assertEquals(0, this.inputSignal.size());
        this.inputSignal.add(this.rawInput.get(0));
        assertEquals(1, this.inputSignal.size());
        this.inputSignal.add(this.rawInput.get(1));
        assertEquals(2, this.inputSignal.size());
    }

    @Test
    void addAll() {
        assertEquals(0, this.inputSignal.size());
        this.inputSignal.addAll(rawInput);
        assertEquals(rawInput.size(), this.inputSignal.size());
    }

    @Test
    void testAddAll() {
        assertEquals(0, this.inputSignal.size());
        this.inputSignal.addAll(Word.fromList(rawInput));
        assertEquals(rawInput.size(), this.inputSignal.size());
    }

    @Test
    void duration() {
        assertEquals(0.0, this.inputSignal.duration());
        this.inputSignal.addAll(rawInput);
        assertEquals(18.0, this.inputSignal.duration());
    }

    @Test
    void testToString() {
        this.inputSignal.addAll(this.rawInput);
        String expectedString = "[0.0 100.0 0.0; 2.0 100.0 0.0; 4.0 100.0 0.0; 6.0 100.0 0.0; 8.0 100.0 0.0; 10.0 100.0 0.0; 12.0 100.0 0.0; 14.0 100.0 0.0; 16.0 100.0 0.0; 18.0 0.0 0.0]";
        assertEquals(expectedString, this.inputSignal.toString());
    }

    @Test
    void size() {
        assertEquals(0, this.inputSignal.size());
        this.inputSignal.add(this.rawInput.get(0));
        assertEquals(1, this.inputSignal.size());
        this.inputSignal.add(this.rawInput.get(1));
        assertEquals(2, this.inputSignal.size());
    }

    @Test
    void clear() {
        this.inputSignal.addAll(rawInput);
        assertEquals(rawInput.size(), this.inputSignal.size());
        this.inputSignal.clear();
        assertEquals(0, this.inputSignal.size());
    }

    @Test
    void get() {
        this.inputSignal.addAll(rawInput);
        assertEquals(rawInput.size(), this.inputSignal.size());
        assertEquals(rawInput.get(0), this.inputSignal.get(0));
        for (int i = 0; i < rawInput.size(); i++) {
            assertEquals(rawInput.get(i), this.inputSignal.get(i));
        }
    }

    @Test
    void testLinearInterpolate() {
        // prepare input
        this.inputSignal.addAll(rawInput);
        // interpolate with step = 1.0
        Signal interp = this.inputSignal.linearInterpolate(1.0);
        // expected 19 points (timestamps 0 through 18)
        assertEquals(19, interp.size());
        // check points 0..16: value should stay at 100.0, 0.0
        for (int i = 0; i <= 16; i++) {
            assertEquals((double) i, interp.getTimestamps().get(i));
            List<Double> v = interp.get(i);
            assertEquals(100.0, v.get(0));
            assertEquals(0.0, v.get(1));
        }
        // check intermediate at t=17 -> should be halfway between 100 and 0
        assertEquals(17.0, interp.getTimestamps().get(17));
        List<Double> v17 = interp.get(17);
        assertEquals(50.0, v17.get(0));
        assertEquals(0.0, v17.get(1));
        // final point at t=18 should match the last raw input (0.0, 0.0)
        assertEquals(18.0, interp.getTimestamps().get(18));
        List<Double> v18 = interp.get(18);
        assertEquals(0.0, v18.get(0));
        assertEquals(0.0, v18.get(1));
    }
}
