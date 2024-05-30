package net.maswag.falcaun;

import lombok.RequiredArgsConstructor;
import net.maswag.falcaun.ExtendedSignalMapperLexer;
import net.maswag.falcaun.ExtendedSignalMapperParser;
import net.maswag.falcaun.ExtendedSignalMapperVisitor;
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
    final private List<Function<ExtendedIOSignalPiece<List<Double>>, List<Double>>> sigMap;

    public ExtendedSignalMapper() {
        this.sigMap = Collections.emptyList();
    }

    /**
     * @throws IllegalArgumentException if the given signal is not an instance of ExtendedIOSignalPiece
     */
    //@ requires 0 <= index < size()
    public double apply(int index, IOSignalPiece<List<Double>> concreteSignal) {
        if (!(concreteSignal instanceof ExtendedIOSignalPiece)) {
            throw new IllegalArgumentException("The given signal is not an instance of ExtendedIOSignalPiece");
        }
        return this.sigMap.get(index).apply((ExtendedIOSignalPiece<List<Double>>) concreteSignal).get(0);
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
        return ExtendedSignalMapper.parse(reader.lines().collect(Collectors.toList()));
    }

    public static ExtendedSignalMapper parse(List<String> mapperDefinitions) {
        List<Function<ExtendedIOSignalPiece<List<Double>>, List<Double>>> rawList =
                mapperDefinitions.stream().map(ExtendedSignalMapper::lineParse).collect(Collectors.toList());

        return new ExtendedSignalMapper(rawList);
    }

    static Function<ExtendedIOSignalPiece<List<Double>>, List<Double>> lineParse(String line) {
        ExtendedSignalMapperVisitor<Function<ExtendedIOSignalPiece<List<Double>>, List<Double>>> visitor = new ExtendedSignalMapperVisitorImpl();
        return parseSignalMapperImpl(line, visitor);
    }

    private static Function<ExtendedIOSignalPiece<List<Double>>, List<Double>> parseSignalMapperImpl(String line, ExtendedSignalMapperVisitor<Function<ExtendedIOSignalPiece<List<Double>>, List<Double>>> visitor) {
        CharStream stream = CharStreams.fromString(line);
        ExtendedSignalMapperLexer lexer = new ExtendedSignalMapperLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        ExtendedSignalMapperParser parser = new net.maswag.falcaun.ExtendedSignalMapperParser(tokens);
        ParseTree tree = parser.expr();
        return visitor.visit(tree);
    }
}
