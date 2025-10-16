package net.maswag.falcaun;

import com.google.common.primitives.Chars;
import lombok.Getter;
import lombok.NonNull;
import lombok.Setter;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * A class for mapping output values to characters.
 * This class is similar to OutputMapperReader but can be instantiated directly from a List&lt;List&lt;Double&gt;&gt;.
 * It maintains the same behavior regarding tracking "largest" characters for out-of-range values.
 */
@Getter
public class OutputMapper {
    private List<List<Double>> parsedData;
    private List<Character> largest;
    private List<Map<Character, Double>> outputMapper;

    /**
     * <p>Constructor for OutputMapper from a file.</p>
     *
     * @param filename The name of the file to read.
     * @throws IOException if an error occurs while reading the file.
     */
    public OutputMapper(String filename) throws IOException {
        this(AbstractMapperReader.rawParse(filename));
    }

    /**
     * <p>Constructor for OutputMapper from data.</p>
     *
     * @param data a {@link java.util.List} object containing the parsed data.
     */
    public OutputMapper(List<List<Double>> data) {
        this.parsedData = data;
        this.parse();
    }

    public OutputMapper(@NonNull List<Map<Character, Double>> outputMapper, @NonNull List<Character> largest) {
        if (outputMapper.size() != largest.size()) {
            throw new IllegalArgumentException("Output mapper and largest character list must have the same size.");
        }
        this.outputMapper = sortOutputMappings(outputMapper);
        this.largest = new ArrayList<>(largest);
    }

    /**
     * Parses the data and creates the output mapper.
     * This method initializes the character mapping and tracks the "largest" characters.
     */
    protected void parse() {
        char[] charList = new char[parsedData.size()];
        Arrays.fill(charList, 'a');

        outputMapper = sortOutputMappings(AbstractMapperReader.assignCharacters(parsedData, charList));

        largest = new ArrayList<>(Chars.asList(charList));
    }

    private static List<Map<Character, Double>> sortOutputMappings(List<Map<Character, Double>> mappings) {
        return mappings.stream()
            .map(OutputMapper::sortByValue)
            .collect(Collectors.toCollection(ArrayList::new));
    }

    private static Map<Character, Double> sortByValue(Map<Character, Double> mapping) {
        return mapping.entrySet()
            .stream()
            .sorted(Map.Entry.comparingByValue())
            .collect(Collectors.toMap(
                Map.Entry::getKey,
                Map.Entry::getValue,
                (existing, replacement) -> existing,
                LinkedHashMap::new
            ));
    }
}