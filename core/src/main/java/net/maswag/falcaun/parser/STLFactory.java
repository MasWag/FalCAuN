package net.maswag.falcaun.parser;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import net.maswag.falcaun.parser.TemporalLogic.STLCost;
import net.maswag.falcaun.parser.TemporalLogic;
import net.maswag.falcaun.parser.STLLexer;
import net.maswag.falcaun.parser.STLParser;
import net.maswag.falcaun.parser.STLVisitor;

import java.util.List;
import java.util.Map;

public class STLFactory {
    /**
     * <p>parse an STL formula using mappers</p>
     *
     * @param stlFormula   a {@link java.lang.String} object.
     * @param outputMapper a {@link java.util.List} object.
     * @param largest      a {@link java.util.List} object.
     * @return a {@link TemporalLogic.STLCost} object.
     */
    public TemporalLogic.STLCost parse(String stlFormula,
                                       List<Map<Character, Double>> inputMapper,
                                       List<Map<Character, Double>> outputMapper,
                                       List<Character> largest) {
        STLVisitor<TemporalLogic.STLCost> visitor = new STLVisitorImpl(inputMapper, outputMapper, largest);
        return parseImpl(stlFormula, visitor);
    }

    /**
     * <p>parse an STL formula without setting the mapper</p>
     *
     * @param formula a {@link java.lang.String} object.
     * @return a {@link TemporalLogic.STLCost} object.
     */
    public TemporalLogic.STLCost parse(String formula) {
        STLVisitor<TemporalLogic.STLCost> visitor = new STLVisitorImpl();
        return parseImpl(formula, visitor);
    }

    private static TemporalLogic.STLCost parseImpl(String formula,
                                                   STLVisitor<TemporalLogic.STLCost> visitor) {
        CharStream stream = CharStreams.fromString(formula);
        STLLexer lexer = new STLLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        STLParser parser = new STLParser(tokens);
        ParseTree tree = parser.expr();
        return visitor.visit(tree);
    }
}
