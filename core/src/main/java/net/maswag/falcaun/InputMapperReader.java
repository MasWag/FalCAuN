package net.maswag.falcaun;

import java.io.IOException;
import java.util.List;
import java.util.Map;

/**
 * A class for reading and parsing input mapper data from files.
 *
 * @deprecated Use {@link InputMapper} instead. This class will be removed in a future release.
 *             It now uses InputMapper internally for backward compatibility.
 */
@Deprecated
public class InputMapperReader extends AbstractMapperReader {
    /**
     * Parses input mapper data from a file.
     *
     * @param filename The name of the file to read.
     * @return A list of maps from characters to double values.
     * @throws IOException if an error occurs while reading the file.
     * @deprecated Use {@link InputMapper#make(List)} with {@link AbstractMapperReader#rawParse(String)} instead.
     */
    @Deprecated
    public static List<Map<Character, Double>> parse(String filename) throws IOException {
        List<List<Double>> parsedData = rawParse(filename);
        return InputMapperReader.make(parsedData);
    }

    /**
     * Creates a list of maps from characters to double values from a list of lists of double values.
     *
     * @param data The list of lists of double values to convert.
     * @return A list of maps from characters to double values.
     * @deprecated Use {@link InputMapper#make(List)} instead.
     */
    @Deprecated
    public static List<Map<Character, Double>> make(List<List<Double>> data) {
        // Use InputMapper internally for backward compatibility
        return InputMapper.make(data);
    }
}
