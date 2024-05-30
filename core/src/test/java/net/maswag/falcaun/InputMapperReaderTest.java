package net.maswag.falcaun;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.*;

import static org.junit.jupiter.api.Assertions.assertEquals;

class InputMapperReaderTest {

    @Test
    void parse() throws IOException {
        String path = "../example/AT.imap.tsv";
        List<Map<Character, Double>> result = InputMapperReader.parse(path);
        Map<Character, Double> mapper1 = new HashMap<>();
        mapper1.put('a', 0.0);
        mapper1.put('b', 100.0);

        Map<Character, Double> mapper2 = new HashMap<>();
        mapper2.put('a', 0.0);
        mapper2.put('b', 325.0);

        List<Map<Character, Double>> expected = new ArrayList<>(Arrays.asList(mapper1, mapper2));
        assertEquals(expected, result);
    }
}