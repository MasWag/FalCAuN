package net.maswag;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.util.*;
import java.util.stream.Collectors;

class AbstractMapperReader {
    public static List<List<Double>> rawParse(String filename) throws IOException {
        return Files.lines(FileSystems.getDefault().getPath(filename)).map(
                s -> Arrays.stream(s.split("\\s+"))).map(
                stream -> stream.map(str -> str.equals("inf") ? null : Double.parseDouble(str)).collect(Collectors.toList())).collect(Collectors.toList());
    }

    public static ArrayList<Map<Character, Double>> assignCharacters(List<List<Double>> parsedData, char[] charList) {
        ArrayList<Map<Character, Double>> assignedMapper = new ArrayList<>(parsedData.size());

        for (int i = 0; i < parsedData.size(); i++) {
            Map<Character, Double> currentMap = new HashMap<>();

            for (int j = 0; j < parsedData.get(i).size(); j++) {
                if (parsedData.get(i).get(j) != null) {
                    currentMap.put(charList[i]++, parsedData.get(i).get(j));
                }
            }

            assignedMapper.add(currentMap);
        }

        return assignedMapper;
    }
}
