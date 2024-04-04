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
public class SignalMapper {
    final private List<Function<IOSignalPiece<List<Double>>, Double>> sigMap;

    public SignalMapper() {
        this.sigMap = Collections.emptyList();
    }


    //@ requires 0 <= index < size()
    public double apply(int index, IOSignalPiece<List<Double>> concreteSignal) {
        return this.sigMap.get(index).apply(concreteSignal);
    }

    //@ ensures \result >= 0
    public int size() {
        return this.sigMap.size();
    }

    public static SignalMapper parse(String filename) throws IOException {
        List<Function<IOSignalPiece<List<Double>>, Double>> rawList = new BufferedReader(
                new InputStreamReader(new FileInputStream(filename))).lines().map(SignalMapper::lineParse).collect(Collectors.toList());

        return new SignalMapper(rawList);
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
