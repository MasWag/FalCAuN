package net.maswag.falcaun;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Abstract class for reading and parsing mapper data from files.
 * This class provides utility methods to read raw data from a file, parse it into lists of doubles,
 * and assign characters to the parsed data based on a provided character list.
 */
class AbstractMapperReader {
    /**
     * Default constructor for AbstractMapperReader.
     * This class only provides static utility methods, so no initialization is needed.
     */
    AbstractMapperReader() {
        // Default constructor
    }
    /**
     * Parses raw data from a file into a list of lists of doubles.
     *
     * @param filename The name of the file to read and parse.
     * @return A list of lists of doubles, where each inner list represents a line of parsed data.
     * @throws IOException If an I/O error occurs while reading the file.
     */
    public static List<List<Double>> rawParse(String filename) throws IOException {
        return Files.lines(FileSystems.getDefault().getPath(filename)).map(
                s -> Arrays.stream(s.split("\\s+"))).map(
                stream -> stream.map(str -> str.equals("inf") ? null : Double.parseDouble(str)).collect(Collectors.toList())).collect(Collectors.toList());
    }

    /**
     * Assigns characters to the parsed data based on a provided character list.
     *
     * @param parsedData A list of lists of doubles, where each inner list represents a line of parsed data.
     * @param charList   An array of characters to assign to the parsed data.
     * @return An ArrayList of maps, where each map assigns characters to the corresponding values in the parsed data.
     */
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
