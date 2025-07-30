package net.maswag.falcaun.parser;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import net.maswag.falcaun.parser.TemporalLogic.LTLFormula;
import net.maswag.falcaun.parser.TemporalLogic.STLCost;
import net.maswag.falcaun.parser.LTLVisitor;
import net.maswag.falcaun.parser.LTLLexer;
import net.maswag.falcaun.parser.LTLParser;

/**
 * This class provides a method to parse an LTL (Linear Temporal Logic) formula.
 * The format is compatible with LTSmin. Its parser is generated using ANTLR.
 * 
 * @see TemporalLogic
 *
 */
public class LTLFactory {
    /**
     * <p>parse an LTL formula</p>
     *
     * @param formula a {@link String} object.
     * @return a {@link TemporalLogic.LTLFormula} object.
     */
    public TemporalLogic.LTLFormula parse(String formula) {
        LTLVisitor<TemporalLogic.LTLFormula> visitor = new LTLVisitorImpl();
        CharStream stream = CharStreams.fromString(formula);
        LTLLexer lexer = new LTLLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        LTLParser parser = new LTLParser(tokens);
        ParseTree tree = parser.expr();
        return visitor.visit(tree);
    }
}
