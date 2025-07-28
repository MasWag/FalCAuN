package net.maswag.falcaun;

import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

/**
 * InputMapperReader is a utility class for reading input mappings from a file.
 */
public class InputMapperReader extends AbstractMapperReader {
    /**
     * Parses the input mapping from a file and returns a list of mappings.
     * Each {@code Map} contains characters as keys and their corresponding concrete values as values.
     * They are constructed by {@link #make(List)}.
     *
     * @param filename The name of the file containing the input mapping data.
     * @return A list of maps representing the input mappings.
     * @throws IOException If an I/O error occurs while reading the file.
     */
    public static List<Map<Character, Double>> parse(String filename) throws IOException {
        List<List<Double>> parsedData = rawParse(filename);
        return InputMapperReader.make(parsedData);
    }

    /**
     * Constructs the input mapper from the given concrete value lists.
     * This method assigns characters to the concrete values.
     *
     * @param data Each dimension of data is an ascending list of concrete values.
     * @return A list of maps, where each map assigns characters to the corresponding values in the parsed data.
     */
    public static List<Map<Character, Double>> make(List<List<Double>> data) {
        char[] charList = new char[data.size()];
        Arrays.fill(charList, 'a');

        return assignCharacters(data, charList);
    }
}
