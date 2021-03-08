package org.group_mmm;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class SignalMapperTest {
    private final String PWD = System.getenv("PWD");
    private final String sigMapName = PWD + "/src/test/resources/sigMap.txt";
    SignalMapper sigMap;
    List<Double> concreteSignal;

    @BeforeEach
    void setUp() {
        Function<List<Double>, Double> diff = a -> a.get(0) - a.get(1);
        sigMap = new SignalMapper(Collections.singletonList(diff));
        concreteSignal = new ArrayList<>();
        concreteSignal.add(2.0);
        concreteSignal.add(-4.2);
        concreteSignal.add(0.4);
    }

    @Test
    void apply() {
        assertEquals(6.2, sigMap.apply(0, concreteSignal));
        // sigMap should be applied to an index smaller than the size of the SigMap. Otherwise, it throws IndexOutOfBoundsException.
        assertThrows(IndexOutOfBoundsException.class, () -> sigMap.apply(2, concreteSignal));
    }

    @Test
    void size() {
        assertEquals(1, sigMap.size());
    }

    @Test
    void parse() throws IOException {
        sigMap = SignalMapper.parse(sigMapName);
        assertEquals(2, sigMap.size());
        assertEquals(2.0 + 0.4, sigMap.apply(0, concreteSignal));
        assertEquals(-4.2 - 0.4 * 2.0, sigMap.apply(1, concreteSignal));
        assertThrows(IndexOutOfBoundsException.class, () -> sigMap.apply(2, concreteSignal));
    }
}