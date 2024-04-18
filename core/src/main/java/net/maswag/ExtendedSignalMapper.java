package net.maswag;

import lombok.RequiredArgsConstructor;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
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
public class ExtendedSignalMapper implements SignalMapper {
    final private List<Function<ExtendedIOSignalPiece<List<Double>>, Double>> sigMap;

    public ExtendedSignalMapper() {
        this.sigMap = Collections.emptyList();
    }

    //@ requires 0 <= index < size()
    public double apply(int index, IOSignalPiece<List<Double>> concreteSignal) {
        return this.sigMap.get(index).apply((ExtendedIOSignalPiece<List<Double>>) concreteSignal);
    }

    //@ ensures \result >= 0
    public int size() {
        return this.sigMap.size();
    }

    public static ExtendedSignalMapper parse(String filename) throws IOException {
        return ExtendedSignalMapper.parse(new BufferedReader(
                new InputStreamReader(new FileInputStream(filename))));
    }

    public static ExtendedSignalMapper parse(BufferedReader reader) {
        List<Function<ExtendedIOSignalPiece<List<Double>>, Double>> rawList =
                reader.lines().map(ExtendedSignalMapper::lineParse).collect(Collectors.toList());

        return new ExtendedSignalMapper(rawList);
    }

    static Function<ExtendedIOSignalPiece<List<Double>>, Double> lineParse(String line) {
        ExtendedSignalMapperVisitor<Function<ExtendedIOSignalPiece<List<Double>>, Double>> visitor = new ExtendedSignalMapperVisitorImpl();
        return parseSignalMapperImpl(line, visitor);
    }

    private static Function<ExtendedIOSignalPiece<List<Double>>, Double> parseSignalMapperImpl(String line, ExtendedSignalMapperVisitor<Function<ExtendedIOSignalPiece<List<Double>>, Double>> visitor) {
        CharStream stream = CharStreams.fromString(line);
        ExtendedSignalMapperLexer lexer = new ExtendedSignalMapperLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        ExtendedSignalMapperParser parser = new net.maswag.ExtendedSignalMapperParser(tokens);
        ParseTree tree = parser.expr();
        return visitor.visit(tree);
    }
}
