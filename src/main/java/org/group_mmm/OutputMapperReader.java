package org.group_mmm;

import com.google.common.primitives.Chars;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.util.*;
import java.util.stream.Collectors;

class OutputMapperReader {
    private String filename;
    private List<List<Double>> parsedData;
    private ArrayList<Character> largest;
    private ArrayList<Map<Character, Double>> outputMapper;

    OutputMapperReader(String filename) {
        this.filename = filename;
    }

    void parse() throws IOException {
        parsedData = Files.lines(FileSystems.getDefault().getPath(filename)).map(
                s -> Arrays.stream(s.split("\\s+"))).map(
                stream -> stream.map(str -> str.equals("inf") ? null : Double.parseDouble(str)).collect(Collectors.toList())).collect(Collectors.toList());
        char[] charList = new char[parsedData.size()];
        Arrays.fill(charList, 'a');

        outputMapper = new ArrayList<>(parsedData.size());

        for (int i = 0; i < parsedData.size(); i++) {
            Map<Character, Double> currentMap = new HashMap<>();

            for (int j = 0; j < parsedData.get(i).size(); j++) {
                if (parsedData.get(i).get(j) != null) {
                    currentMap.put(charList[i]++, parsedData.get(i).get(j));
                }
            }

            outputMapper.add(currentMap);
        }

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
