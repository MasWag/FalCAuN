package org.group_mmm;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.assertEquals;

class InputMapperReaderTest {

    @Test
    void parse() throws IOException {
        String path = "./example/AT.imap.tsv";
        ArrayList<ArrayList<Double>> result = InputMapperReader.parse(path);
        ArrayList<ArrayList<Double>> expected = new ArrayList<>(Arrays.asList(
                new ArrayList<>(Arrays.asList(0.0, 100.0)),
                new ArrayList<>(Arrays.asList(0.0, 325.0))));
        assertEquals(expected, result);
    }
}