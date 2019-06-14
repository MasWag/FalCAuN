package org.group_mmm;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

class InputMapperReader extends AbstractMapperReader {
    static ArrayList<Map<Character, Double>> parse(String filename) throws IOException {
        List<List<Double>> parsedData = rawParse(filename);
        char[] charList = new char[parsedData.size()];
        Arrays.fill(charList, 'a');

        return assignCharacters(parsedData, charList);
    }
}
