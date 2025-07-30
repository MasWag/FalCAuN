package net.maswag.falcaun;

import lombok.RequiredArgsConstructor;
import net.maswag.falcaun.parser.SignalMapperLexer;
import net.maswag.falcaun.parser.SignalMapperParser;
import net.maswag.falcaun.parser.SignalMapperVisitor;
import net.maswag.falcaun.parser.SignalMapperVisitorImpl;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import java.io.*;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * Class to construct pseudo signals from concrete signals
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@RequiredArgsConstructor
public class SimpleSignalMapper implements SignalMapper {
    final private List<Function<IOSignalPiece<List<Double>>, Double>> sigMap;

    public SimpleSignalMapper() {
        this.sigMap = Collections.emptyList();
    }

    //@ requires 0 <= index < size()
    @Override
    public double apply(int index, IOSignalPiece<List<Double>> concreteSignal) {
        return this.sigMap.get(index).apply(concreteSignal);
    }

    //@ ensures \result >= 0
    @Override
    public int size() {
        return this.sigMap.size();
    }

    /**
     * Get {@link SignalMapper} by parsing the given file
     * 
     * @param filename The filename to parse
     * @return The {@link SignalMapper} object constructed from the file
     * @throws IOException
     */
    public static SignalMapper parse(String filename) throws IOException {
        return SimpleSignalMapper.parse(new BufferedReader(
                new InputStreamReader(new FileInputStream(filename))));
    }

    /**
     * Get {@link SignalMapper} by parsing from a {@link BufferedReader}
     * 
     * @param reader
     */
    public static SignalMapper parse(BufferedReader reader) {
        return SimpleSignalMapper.parse(reader.lines().collect(Collectors.toList()));
    }

    /**
     * Get {@link SignalMapper} by parsing a list of strings.
     * 
     * @param mapperDefinitions The list of strings
     */
    public static SignalMapper parse(List<String> mapperDefinitions) {
        List<Function<IOSignalPiece<List<Double>>, Double>> rawList =
                mapperDefinitions.stream().map(SimpleSignalMapper::lineParse).collect(Collectors.toList());

        return new SimpleSignalMapper(rawList);
    }

    static Function<IOSignalPiece<List<Double>>, Double> lineParse(String line) {
        SignalMapperVisitor<Function<IOSignalPiece<List<Double>>, Double>> visitor = new SignalMapperVisitorImpl();
        return parseSignalMapperImpl(line, visitor);
    }

    private static Function<IOSignalPiece<List<Double>>, Double> parseSignalMapperImpl(String line, SignalMapperVisitor<Function<IOSignalPiece<List<Double>>, Double>> visitor) {
        CharStream stream = CharStreams.fromString(line);
        SignalMapperLexer lexer = new SignalMapperLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        SignalMapperParser parser = new SignalMapperParser(tokens);
        ParseTree tree = parser.expr();
        return visitor.visit(tree);
    }
}
