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
 * @deprecated Use {@link OutputMapper} instead. This class will be removed in a future release.
 * It now uses OutputMapper internally for backward compatibility.
 */
@Getter
@Deprecated
public class OutputMapperReader extends AbstractMapperReader {
    private final List<List<Double>> parsedData;
    private List<Character> largest;
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
     * Parses the data and creates the output mapper.
     *
     * @deprecated You do not need to call this method directly anymore.
     */
    @Deprecated
    public void parse() {
        this.outputMapper = delegate.getOutputMapper();
        
        // Get the largest characters from the delegate
        this.largest = delegate.getLargest();
    }
}
