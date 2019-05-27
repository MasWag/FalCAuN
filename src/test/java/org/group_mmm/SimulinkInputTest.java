package org.group_mmm;

import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.BeforeEach;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class SimulinkInputTest {
    private ArrayList<Map<Character, Double>> inputMapper;

    @BeforeEach
    void setUp() {
        Map<Character, Double> mapper1 = new HashMap<>();
        mapper1.put('a', 10.0);
        mapper1.put('b', 20.0);
        Map<Character, Double> mapper2 = new HashMap<>();
        mapper2.put('a', -100.0);
        mapper2.put('b', 0.0);
        mapper2.put('c', 100.0);
        inputMapper = new ArrayList<>(Arrays.asList(mapper1, mapper2));
    }

    @org.junit.jupiter.api.Test
    void toString1() {
        for (Character c1 : Arrays.asList('a', 'b')) {
            for (Character c2 : Arrays.asList('a', 'b', 'c')) {
                String expected = String.valueOf(c1) + c2;
                SimulinkInput input = new SimulinkInput(inputMapper, expected);
                assertEquals(input.toString(), expected);
            }
        }
    }

    @org.junit.jupiter.api.Test
    void toArrayList() {
        for (Map.Entry<Character, Double> c1 : inputMapper.get(0).entrySet()) {
            for (Map.Entry<Character, Double> c2 : inputMapper.get(1).entrySet()) {
                String abstractInput = String.valueOf(c1.getKey()) + c2.getKey();
                ArrayList<Double> expected = new ArrayList<>(Arrays.asList(c1.getValue(), c2.getValue()));
                SimulinkInput input = new SimulinkInput(inputMapper, abstractInput);
                assertEquals(expected, input.toArrayList());
            }
        }
    }

    @org.junit.jupiter.api.Test()
    void toArrayListDifferentLength() {
        assertThrows(AssertionError.class, () -> new SimulinkInput(inputMapper, "a"));
        assertThrows(AssertionError.class, () -> new SimulinkInput(inputMapper, "aaa"));
    }

    @org.junit.jupiter.api.Test
    void toArrayListOutOfScope() {
        SimulinkInput input = new SimulinkInput(inputMapper, "cd");
        Assertions.assertThat(input.toArrayList()).isNull();
    }
}