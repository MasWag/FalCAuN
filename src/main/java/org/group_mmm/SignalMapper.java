package org.group_mmm;

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
    final private List<Function<List<Double>, Double>> sigMap;

    public SignalMapper() {
        this.sigMap = Collections.emptyList();
    }


    //@ requires 0 <= index < size()
    public double apply(int index, List<Double> concreteSignal) {
        return this.sigMap.get(index).apply(concreteSignal);
    }

    //@ ensures \result >= 0
    public int size() {
        return this.sigMap.size();
    }

    public static SignalMapper parse(String filename) throws IOException {
        List<Function<List<Double>, Double>> rawList = new BufferedReader(
                new InputStreamReader(new FileInputStream(filename))).lines().map(SignalMapper::lineParse).collect(Collectors.toList());

        return new SignalMapper(rawList);
    }

    static Function<List<Double>, Double> lineParse(String line) {
        org.group_mmm.SignalMapperVisitor<Function<List<Double>, Double>> visitor = new SignalMapperVisitorImpl();
        return parseSignalMapperImpl(line, visitor);
    }

    private static Function<List<Double>, Double> parseSignalMapperImpl(String line,
                                                                        org.group_mmm.SignalMapperVisitor<Function<List<Double>, Double>> visitor) {
        CharStream stream = CharStreams.fromString(line);
        org.group_mmm.SignalMapperLexer lexer = new org.group_mmm.SignalMapperLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        org.group_mmm.SignalMapperParser parser = new org.group_mmm.SignalMapperParser(tokens);
        ParseTree tree = parser.expr();
        return visitor.visit(tree);
    }
}
