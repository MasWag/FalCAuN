package org.group_mmm;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.*;

import static org.junit.jupiter.api.Assertions.assertEquals;

class OutputMapperReaderTest {
    private OutputMapperReader reader;

    @BeforeEach
    void setUp() throws IOException {
        String path = "./example/AT_S4.omap.tsv";
        reader = new OutputMapperReader(path);
        reader.parse();
    }

    @Test
    void parse() {
        List<List<Double>> result = reader.getParsedData();
        List<List<Double>> expected = Arrays.asList(
                Arrays.asList(65.0, 100.0, null),
                Collections.singletonList(null),
                Collections.singletonList(null));
        assertEquals(expected, result);
    }

    @Test
    void getOutputMapper() {
        ArrayList<Map<Character, Double>> result = reader.getOutputMapper();
        Map<Character, Double> velocityMap = new HashMap<>();
        velocityMap.put('a', 65.0);
        velocityMap.put('b', 100.0);
        Map<Character, Double> rotationMap = new HashMap<>();
        Map<Character, Double> gearMap = new HashMap<>();

        ArrayList<Map<Character, Double>> expected = new ArrayList<>(Arrays.asList(
                velocityMap, rotationMap, gearMap));

        assertEquals(expected, result);
    }

    @Test
    void getLargest() {
        ArrayList<Character> result = reader.getLargest();
        ArrayList<Character> expected = new ArrayList<>(Arrays.asList('c', 'a', 'a'));
        assertEquals(expected, result);
    }
}