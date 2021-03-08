package org.group_mmm;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class SignalMapperTest {
    SignalMapper sigMap;

    @BeforeEach
    void setUp() {
        Function<List<Double>, Double> diff = a -> a.get(0) - a.get(1);
        sigMap = new SignalMapper(Collections.singletonList(diff));
    }

    @Test
    void apply() {
        List<Double> concreteSignal = new ArrayList<>();
        concreteSignal.add(2.0);
        concreteSignal.add(-4.2);
        assertEquals(6.2, sigMap.apply(0, concreteSignal));
        // sigMap should be applied to an index smaller than the size of the SigMap. Otherwise, it throws IndexOutOfBoundsException.
        assertThrows(IndexOutOfBoundsException.class, () -> sigMap.apply(2, concreteSignal));
    }

    @Test
    void size() {
        assertEquals(1, sigMap.size());
    }
}