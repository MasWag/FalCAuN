package net.maswag.falcaun;

import com.google.common.primitives.Chars;
import lombok.Getter;

import java.io.IOException;
import java.util.*;

/**
 * {@code OutputMapperReader} manages output mapping,
 * converting abstract outputs into concrete values.
 * 
 * {@code outputMapper} is a list of mappings from an abstract alphabet character to the concrete value.
 * {@code largest} is a list of abstract alphabet chars representing a larger concrete value
 * than any of the given concrete values.
 * 
 * After construction, call {@link #parse()} to initialize the mappings
 * and then {@link #outputMapper} and {@link #largest} will be available.
 * 
 */
public class OutputMapperReader extends AbstractMapperReader {
    private String filename;
    @Getter
    private List<List<Double>> parsedData;

    /**
     * List of characters representing a larger value than any of the concrete values.
     * For example, given the concrete values {@literal [1.0, 2.0, 3.0]},
     * the character in {@code largest} represents a value in range {@literal (3.0, +inf)}
     */
    @Getter
    private List<Character> largest;

    /**
     * The output mapper, a list of mappings from an abstract alphabet character to
     * its corresponding concrete value.
     */
    @Getter
    private List<Map<Character, Double>> outputMapper;

    /**
     * @param filename The name of the file that contains the output mapping data.
     */
    public OutputMapperReader(String filename) {
        this.filename = filename;
    }

    /**
     * Constructor for OutputMapperReader from data
     * 
     * @param data Each dimension of data is an ascending list of concrete values
     */
    public OutputMapperReader(List<List<Double>> data) {
        this.parsedData = data;
    }

    /**
     * Constructs the output mapper {@code outputMapper} and {@code largest} from the given concrete value lists.
     * This method assigns characters to the concrete values
     * and determines the largest character for each output dimension.
     * When the instance is constructed by filename, this method reads and parses the specified file,
     * then constructs them from the parsed data.
     * 
     * @throws IOException if an I/O error occurs while reading the file
     */
    public void parse() throws IOException {
        if (Objects.isNull(parsedData)) {
            parsedData = rawParse(filename);
        }
        char[] charList = new char[parsedData.size()];
        Arrays.fill(charList, 'a');

        outputMapper = assignCharacters(parsedData, charList);

        largest = new ArrayList<>(Chars.asList(charList));
    }
}
