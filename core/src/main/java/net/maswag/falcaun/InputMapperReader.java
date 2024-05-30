package net.maswag.falcaun;

import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

public class InputMapperReader extends AbstractMapperReader {
    static List<Map<Character, Double>> parse(String filename) throws IOException {
        List<List<Double>> parsedData = rawParse(filename);
        return InputMapperReader.make(parsedData);
    }

    public static List<Map<Character, Double>> make(List<List<Double>> data) {
        char[] charList = new char[data.size()];
        Arrays.fill(charList, 'a');

        return assignCharacters(data, charList);
    }
}
