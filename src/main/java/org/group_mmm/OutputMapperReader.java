package org.group_mmm;

import com.google.common.primitives.Chars;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

class OutputMapperReader extends AbstractMapperReader {
    private String filename;
    private ArrayList<Character> largest;
    private List<List<Double>> parsedData;
    private ArrayList<Map<Character, Double>> outputMapper;

    OutputMapperReader(String filename) {
        this.filename = filename;
    }

    void parse() throws IOException {
        parsedData = rawParse(filename);
        char[] charList = new char[parsedData.size()];
        Arrays.fill(charList, 'a');

        outputMapper = assignCharacters(parsedData, charList);

        largest = new ArrayList<>(Chars.asList(charList));
    }

    List<List<Double>> getParsedData() {
        return parsedData;
    }

    ArrayList<Character> getLargest() {
        return largest;
    }

    ArrayList<Map<Character, Double>> getOutputMapper() {
        return outputMapper;
    }
}
