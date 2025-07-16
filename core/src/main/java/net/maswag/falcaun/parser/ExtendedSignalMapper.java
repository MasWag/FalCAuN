package net.maswag.falcaun.parser;

import lombok.RequiredArgsConstructor;
import net.maswag.falcaun.ExtendedIOSignalPiece;
import net.maswag.falcaun.IOSignalPiece;
import net.maswag.falcaun.parser.SignalMapper;
import net.maswag.falcaun.parser.ExtendedSignalMapperLexer;
import net.maswag.falcaun.parser.ExtendedSignalMapperParser;
import net.maswag.falcaun.parser.ExtendedSignalMapperVisitor;

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

    /**
     * Constructs a new ExtendedSignalMapper with an empty list of signal mappers.
     */
    public ExtendedSignalMapper() {
        this.sigMap = Collections.emptyList();
    }

    /**
     * Applies the signal mapper to the specified index and concrete signal.
     *
     * @param index          the index of the signal mapper to apply
     * @param concreteSignal the concrete signal to apply the signal mapper to
     * @return the result of applying the signal mapper
     * @throws IllegalArgumentException if the given signal is not an instance of ExtendedIOSignalPiece
     */
    public double apply(int index, IOSignalPiece<List<Double>> concreteSignal) {
        if (!(concreteSignal instanceof ExtendedIOSignalPiece)) {
            throw new IllegalArgumentException("The given signal is not an instance of ExtendedIOSignalPiece");
        }
        return this.sigMap.get(index).apply((ExtendedIOSignalPiece<List<Double>>) concreteSignal).get(0);
    }

    /**
     * Returns the size of the signal mapper list.
     *
     * @return the size of the signal mapper list
     */
    public int size() {
        return this.sigMap.size();
    }

    /**
     * Parses the signal mapper from the specified file.
     *
     * @param filename the name of the file to parse
     * @return the parsed signal mapper
     * @throws IOException if an I/O error occurs
     */
    public static ExtendedSignalMapper parse(String filename) throws IOException {
        return ExtendedSignalMapper.parse(new BufferedReader(
                new InputStreamReader(new FileInputStream(filename))));
    }

    /**
     * Parses the signal mapper from the specified BufferedReader.
     *
     * @param reader the BufferedReader to parse
     * @return the parsed signal mapper
     */
    public static ExtendedSignalMapper parse(BufferedReader reader) {
        return ExtendedSignalMapper.parse(reader.lines().collect(Collectors.toList()));
    }

    /**
     * Parses the signal mapper from the specified list of mapper definitions.
     *
     * @param mapperDefinitions the list of mapper definitions to parse
     * @return the parsed signal mapper
     */
    public static ExtendedSignalMapper parse(List<String> mapperDefinitions) {
        List<Function<ExtendedIOSignalPiece<List<Double>>, List<Double>>> rawList =
                mapperDefinitions.stream().map(ExtendedSignalMapper::lineParse).collect(Collectors.toList());

        return new ExtendedSignalMapper(rawList);
    }

    /**
     * Parses a single line of the signal mapper definition.
     *
     * @param line the line to parse
     * @return the parsed signal mapper function
     */
    static Function<ExtendedIOSignalPiece<List<Double>>, List<Double>> lineParse(String line) {
        ExtendedSignalMapperVisitor<Function<ExtendedIOSignalPiece<List<Double>>, List<Double>>> visitor = new ExtendedSignalMapperVisitorImpl();
        return parseSignalMapperImpl(line, visitor);
    }

    /**
     * Parses the signal mapper definition using the specified visitor.
     *
     * @param line   the line to parse
     * @param visitor the visitor to use for parsing
     * @return the parsed signal mapper function
     */
    private static Function<ExtendedIOSignalPiece<List<Double>>, List<Double>> parseSignalMapperImpl(String line, ExtendedSignalMapperVisitor<Function<ExtendedIOSignalPiece<List<Double>>, List<Double>>> visitor) {
        CharStream stream = CharStreams.fromString(line);
        ExtendedSignalMapperLexer lexer = new ExtendedSignalMapperLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        ExtendedSignalMapperParser parser = new ExtendedSignalMapperParser(tokens);
        ParseTree tree = parser.expr();
        return visitor.visit(tree);
    }
}
