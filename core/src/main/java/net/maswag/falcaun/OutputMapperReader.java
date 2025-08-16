package net.maswag.falcaun;

import com.google.common.primitives.Chars;
import lombok.Getter;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

@Getter
public class OutputMapperReader extends AbstractMapperReader {
    private final List<List<Double>> parsedData;
    private List<Character> largest;
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

    public void parse() {
        char[] charList = new char[parsedData.size()];
        Arrays.fill(charList, 'a');

        outputMapper = assignCharacters(parsedData, charList);

        largest = new ArrayList<>(Chars.asList(charList));
    }
}
