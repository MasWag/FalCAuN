package net.maswag.falcaun;

import com.google.common.primitives.Chars;
import lombok.Getter;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

/**
 * A class for reading and parsing output mapper data from files.
 *
 * {@code outputMapper} is a list of mappings from an abstract alphabet character to the concrete value.
 * {@code largest} is a list of abstract alphabet chars representing a larger concrete value
 * than any of the given concrete values.
 * 
 * After construction, call {@link #parse()} to initialize the mappings
 * and then {@link #outputMapper} and {@link #largest} will be available.
 * 
 * @deprecated Use {@link OutputMapper} instead. This class will be removed in a future release.
 * It now uses OutputMapper internally for backward compatibility.
 */
@Getter
@Deprecated
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

    // Internal OutputMapper instance for delegation
    private final OutputMapper delegate;

    /**
     * <p>Constructor for OutputMapperReader.</p>
     *
     * @param filename The name of the file to read.
     * @throws IOException if an error occurs while reading the file.
     * @deprecated Use {@link OutputMapper#OutputMapper(String)} instead.
     */
    @Deprecated
    public OutputMapperReader(String filename) throws IOException {
        this(rawParse(filename));
    }

    /**
     * <p>Constructor for OutputMapperReader from data.</p>
     *
     * @param data a {@link java.util.List} object containing the parsed data.
     * @deprecated Use {@link OutputMapper#OutputMapper(List)} instead.
     */
    @Deprecated
    public OutputMapperReader(List<List<Double>> data) {
        this.parsedData = data;
        // Create delegate OutputMapper
        this.delegate = new OutputMapper(data);
        this.parse();
    }

    /**
     * Constructs the output mapper {@code outputMapper} and {@code largest} from the given concrete value lists.
     * This method assigns characters to the concrete values
     * and determines the largest character for each output dimension.
     * When the instance is constructed by filename, this method reads and parses the specified file,
     * then constructs them from the parsed data.
     *
     * @throws IOException
     * @deprecated You do not need to call this method directly anymore.
     */
    @Deprecated
    public void parse() {
        this.outputMapper = delegate.getOutputMapper();
        
        // Get the largest characters from the delegate
        this.largest = delegate.getLargest();
    }
}
