package net.maswag.falcaun;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.*;

import static org.junit.jupiter.api.Assertions.assertEquals;

class OutputMapperReaderTest {
    private OutputMapperReader reader;

    @BeforeEach
    void setUp() throws IOException {
        String path = "../example/shell/AT_S4.omap.tsv";
        reader = new OutputMapperReader(path);
        reader.parse();
    }

    @Test
    void parse() {
        List<List<Double>> result = reader.getParsedData();
        List<List<Double>> expected = Arrays.asList(
                Arrays.asList(55.0, 65.0, 75.0, 90.0, 100.0, 110.0, null),
                Collections.singletonList(null),
                Collections.singletonList(null));
        assertEquals(expected, result);
    }

    @Test
    void getOutputMapper() {
        List<Map<Character, Double>> result = reader.getOutputMapper();
        Map<Character, Double> velocityMap = new HashMap<>();
        velocityMap.put('a', 55.0);
        velocityMap.put('b', 65.0);
        velocityMap.put('c', 75.0);
        velocityMap.put('d', 90.0);
        velocityMap.put('e', 100.0);
        velocityMap.put('f', 110.0);
        Map<Character, Double> rotationMap = new HashMap<>();
        Map<Character, Double> gearMap = new HashMap<>();

        List<Map<Character, Double>> expected = new ArrayList<>(Arrays.asList(
                velocityMap, rotationMap, gearMap));

        assertEquals(expected, result);
    }

    @Test
    void getLargest() {
        List<Character> result = reader.getLargest();
        List<Character> expected = new ArrayList<>(Arrays.asList('g', 'a', 'a'));
        assertEquals(expected, result);
    }
}