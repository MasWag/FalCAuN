package net.maswag;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;

import static java.lang.Math.abs;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class ExtendedSignalMapperTest {
    SignalMapper sigMap;
    List<Double> concreteSignal;
    List<List<Double>> previousValues;

    @BeforeEach
    void setUp() {
        concreteSignal = new ArrayList<>();
        concreteSignal.add(2.0);
        concreteSignal.add(-4.2);
        concreteSignal.add(0.4);
        previousValues = new ArrayList<>();
        previousValues.add(Arrays.asList(1.0, 2.0, 3.0));
        previousValues.add(Arrays.asList(4.0, 5.0, 6.0));
    }

    @Test
    void parse() throws IOException {
        String sigMapContent = "previous_max_output(2)\n" + "previous_min_output(2)";
        BufferedReader reader = new BufferedReader(new StringReader(sigMapContent));
        sigMap = ExtendedSignalMapper.parse(reader);
        assertEquals(2, sigMap.size());
        assertEquals(Math.max(3.0, 6.0), sigMap.apply(0,
                new ExtendedIOSignalPiece<>(Collections.emptyList(), concreteSignal, previousValues)));
        assertEquals(Math.min(3.0, 6.0), sigMap.apply(1,
                new ExtendedIOSignalPiece<>(Collections.emptyList(), concreteSignal, previousValues)));
    }
}