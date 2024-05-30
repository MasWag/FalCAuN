package net.maswag.falcaun;

import com.google.common.primitives.Chars;
import lombok.Getter;

import java.io.IOException;
import java.util.*;

public class OutputMapperReader extends AbstractMapperReader {
    private String filename;
    @Getter
    private List<List<Double>> parsedData;
    @Getter
    private List<Character> largest;
    @Getter
    private List<Map<Character, Double>> outputMapper;

    public OutputMapperReader(String filename) {
        this.filename = filename;
    }

    /**
     * <p>Constructor for OutputMapperReader from data.</p>
     */
    public OutputMapperReader(List<List<Double>> data) {
        this.parsedData = data;
    }

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
