package net.maswag;

import lombok.RequiredArgsConstructor;
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

    public static SignalMapper parse(String filename) throws IOException {
        return SimpleSignalMapper.parse(new BufferedReader(
                new InputStreamReader(new FileInputStream(filename))));
    }

    public static SignalMapper parse(BufferedReader reader) {
        List<Function<IOSignalPiece<List<Double>>, Double>> rawList =
                reader.lines().map(SimpleSignalMapper::lineParse).collect(Collectors.toList());

        return new SimpleSignalMapper(rawList);
    }

    static Function<IOSignalPiece<List<Double>>, Double> lineParse(String line) {
        net.maswag.SignalMapperVisitor<Function<IOSignalPiece<List<Double>>, Double>> visitor = new SignalMapperVisitorImpl();
        return parseSignalMapperImpl(line, visitor);
    }

    private static Function<IOSignalPiece<List<Double>>, Double> parseSignalMapperImpl(String line, net.maswag.SignalMapperVisitor<Function<IOSignalPiece<List<Double>>, Double>> visitor) {
        CharStream stream = CharStreams.fromString(line);
        net.maswag.SignalMapperLexer lexer = new net.maswag.SignalMapperLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        net.maswag.SignalMapperParser parser = new net.maswag.SignalMapperParser(tokens);
        ParseTree tree = parser.expr();
        return visitor.visit(tree);
    }
}
