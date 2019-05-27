package org.group_mmm;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

class SimulinkOutputTest {
    private ArrayList<Map<Character, Double>> outputMapper;
    private ArrayList<Character> largest;


    @BeforeEach
    void setUp() {
        Map<Character, Double> mapper1 = new HashMap<>();
        mapper1.put('a', 10.0);
        mapper1.put('b', 20.0);
        Map<Character, Double> mapper2 = new HashMap<>();
        mapper2.put('a', -100.0);
        mapper2.put('b', 0.0);
        mapper2.put('c', 100.0);
        outputMapper = new ArrayList<>(Arrays.asList(mapper1, mapper2));
        largest = new ArrayList<>(Arrays.asList('0', '0'));
    }

    @Test
    void toString1() {
        Map<ArrayList<Double>, String> expected = new HashMap<>();
        expected.put(new ArrayList<>(Arrays.asList(-100.0, -200.0)), "aa");
        expected.put(new ArrayList<>(Arrays.asList(-10.0, -20.0)), "ab");
        expected.put(new ArrayList<>(Arrays.asList(-1.0, 20.0)), "ac");
        expected.put(new ArrayList<>(Arrays.asList(10.0, 200.0)), "a0");

        expected.put(new ArrayList<>(Arrays.asList(11.0, -200.0)), "ba");
        expected.put(new ArrayList<>(Arrays.asList(20.0, 0.0)), "bb");
        expected.put(new ArrayList<>(Arrays.asList(12.0, 20.0)), "bc");
        expected.put(new ArrayList<>(Arrays.asList(13.0, 200.0)), "b0");

        expected.put(new ArrayList<>(Arrays.asList(21.0, -100.0)), "0a");
        expected.put(new ArrayList<>(Arrays.asList(211.0, -20.0)), "0b");
        expected.put(new ArrayList<>(Arrays.asList(212.0, 100.0)), "0c");
        expected.put(new ArrayList<>(Arrays.asList(113.0, 200.0)), "00");

        for (Map.Entry<ArrayList<Double>, String> test : expected.entrySet()) {
            SimulinkOutput output = new SimulinkOutput(largest, outputMapper, test.getKey());
            assertEquals(test.getValue(), output.toString());
        }
    }

    @Test
    void toArrayList() {
        ArrayList<Double> expected = new ArrayList<>(Arrays.asList(1000.0, 2000.0));
        SimulinkOutput output = new SimulinkOutput(largest, outputMapper, expected);
        assertEquals(expected, output.toArrayList());
    }
}