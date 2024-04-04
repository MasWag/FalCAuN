package net.maswag;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.List;
import java.util.Map;

import net.maswag.TemporalLogic.STLCost;

public class STLFactory {
    /**
     * <p>parse an STL formula using mappers</p>
     *
     * @param stlFormula   a {@link java.lang.String} object.
     * @param outputMapper a {@link java.util.List} object.
     * @param largest      a {@link java.util.List} object.
     * @return a {@link net.maswag.TemporalLogic.STLCost} object.
     */
    public STLCost parse(String stlFormula,
                         List<Map<Character, Double>> inputMapper,
                         List<Map<Character, Double>> outputMapper,
                         List<Character> largest) {
        net.maswag.STLVisitor<STLCost> visitor = new STLVisitorImpl(inputMapper, outputMapper, largest);
        return parseImpl(stlFormula, visitor);
    }

    /**
     * <p>parse an STL formula without setting the mapper</p>
     *
     * @param formula a {@link java.lang.String} object.
     * @return a {@link net.maswag.TemporalLogic.STLCost} object.
     */
    public STLCost parse(String formula) {
        net.maswag.STLVisitor<STLCost> visitor = new STLVisitorImpl();
        return parseImpl(formula, visitor);
    }

    private static STLCost parseImpl(String formula,
                                     net.maswag.STLVisitor<STLCost> visitor) {
        CharStream stream = CharStreams.fromString(formula);
        net.maswag.STLLexer lexer = new net.maswag.STLLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        net.maswag.STLParser parser = new net.maswag.STLParser(tokens);
        ParseTree tree = parser.expr();
        return visitor.visit(tree);
    }
}
