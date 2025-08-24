package net.maswag.falcaun;

import com.google.common.primitives.Chars;
import lombok.Getter;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

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
@Getter
public class OutputMapperReader extends AbstractMapperReader {
    private final List<List<Double>> parsedData;

    /**
     * List of characters representing a larger value than any of the concrete values.
     * For example, given the concrete values {@literal [1.0, 2.0, 3.0]},
     * the character in {@code largest} represents a value in range {@literal (3.0, +inf)}
     */
    private List<Character> largest;

    /**
     * The output mapper, a list of mappings from an abstract alphabet character to
     * its corresponding concrete value.
     */
    private List<Map<Character, Double>> outputMapper;

    /**
     * <p>Constructor for OutputMapperReader.</p>
     *
     * @param filename The name of the file to read.
     * @throws IOException if an error occurs while reading the file.
     */
    public OutputMapperReader(String filename) throws IOException {
        this(rawParse(filename));
    }

    /**
     * <p>Constructor for OutputMapperReader from data.</p>
     *
     * @param data a {@link java.util.List} object containing the parsed data.
     */
    public OutputMapperReader(List<List<Double>> data) {
        this.parsedData = data;
        this.parse();
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
    public void parse() {
        char[] charList = new char[parsedData.size()];
        Arrays.fill(charList, 'a');

        outputMapper = assignCharacters(parsedData, charList);

        largest = new ArrayList<>(Chars.asList(charList));
    }
}
