package org.group_mmm;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.stream.Collectors;

class InputMapperReader {
    static ArrayList<ArrayList<Double>> parse(String filename) throws IOException {
        return Files.lines(FileSystems.getDefault().getPath(filename)).map(
                s -> Arrays.stream(s.split("\\s+"))).map(
                stream -> stream.map(Double::parseDouble).collect(Collectors.toCollection(ArrayList::new))).collect(Collectors.toCollection(ArrayList::new));
    }
}
