package org.group_mmm;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.*;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;

class SimulinkSULMapperTest {

    private ArrayList<Map<Character, Double>> inputMapper;
    private ArrayList<Map<Character, Double>> outputMapper;
    private ArrayList<Character> largest;
    private SimulinkSULMapper mapper;
    private ArrayList<Function<ArrayList<Double>, Double>> sigMap;


    @Test
    void mapInput() {
        for (Map.Entry<Character, Double> c1 : inputMapper.get(0).entrySet()) {
            for (Map.Entry<Character, Double> c2 : inputMapper.get(1).entrySet()) {
                String abstractInput = String.valueOf(c1.getKey()) + c2.getKey();
                ArrayList<Double> expected = new ArrayList<>(Arrays.asList(c1.getValue(), c2.getValue()));
                ArrayList<Double> result = mapper.mapInput(abstractInput);
                assertEquals(expected, result);
            }
        }
    }

    @Test
    void mapOutput() {
        Map<ArrayList<Double>, String> expected = new HashMap<>();
        expected.put(new ArrayList<>(Arrays.asList(-100.0, -200.0)), "aap");
        expected.put(new ArrayList<>(Arrays.asList(-10.0, -20.0)), "abp");
        expected.put(new ArrayList<>(Arrays.asList(-1.0, 20.0)), "acn");
        expected.put(new ArrayList<>(Arrays.asList(10.0, 200.0)), "a0n");

        expected.put(new ArrayList<>(Arrays.asList(11.0, -200.0)), "bap");
        expected.put(new ArrayList<>(Arrays.asList(20.0, 0.0)), "bbp");
        expected.put(new ArrayList<>(Arrays.asList(12.0, 20.0)), "bcn");
        expected.put(new ArrayList<>(Arrays.asList(13.0, 200.0)), "b0n");

        expected.put(new ArrayList<>(Arrays.asList(21.0, -100.0)), "0ap");
        expected.put(new ArrayList<>(Arrays.asList(211.0, -20.0)), "0bp");
        expected.put(new ArrayList<>(Arrays.asList(212.0, 100.0)), "0cp");
        expected.put(new ArrayList<>(Arrays.asList(113.0, 200.0)), "00n");

        for (Map.Entry<ArrayList<Double>, String> test : expected.entrySet()) {
            String result = mapper.mapOutput(test.getKey());
            assertEquals(test.getValue(), result);
        }
    }

    @Test
    void constructAlphabet() {
    }

    @BeforeEach
    void setUp() {
        {
            Map<Character, Double> mapper1 = new HashMap<>();
            mapper1.put('a', 10.0);
            mapper1.put('b', 20.0);
            Map<Character, Double> mapper2 = new HashMap<>();
            mapper2.put('a', -100.0);
            mapper2.put('b', 0.0);
            mapper2.put('c', 100.0);
            inputMapper = new ArrayList<>(Arrays.asList(mapper1, mapper2));
        }
        Function<ArrayList<Double>, Double> diff = a -> a.get(0) - a.get(1);
        sigMap = new ArrayList<>(Collections.singletonList(diff));
        {
            Map<Character, Double> mapper1 = new HashMap<>();
            mapper1.put('a', 10.0);
            mapper1.put('b', 20.0);
            Map<Character, Double> mapper2 = new HashMap<>();
            mapper2.put('a', -100.0);
            mapper2.put('b', 0.0);
            mapper2.put('c', 100.0);
            Map<Character, Double> mapper3 = new HashMap<>();
            mapper3.put('n', 0.0);
            outputMapper = new ArrayList<>(Arrays.asList(mapper1, mapper2, mapper3));
            largest = new ArrayList<>(Arrays.asList('0', '0', 'p'));
        }
        mapper = new SimulinkSULMapper(inputMapper, largest, outputMapper, sigMap);
    }
}