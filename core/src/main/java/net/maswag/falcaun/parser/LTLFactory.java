package net.maswag.falcaun;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

public class LTLFactory {
    /**
     * <p>parse an LTL formula</p>
     *
     * @param formula a {@link String} object.
     * @return a {@link TemporalLogic.STLCost} object.
     */
    public TemporalLogic.LTLFormula parse(String formula) {
        net.maswag.falcaun.LTLVisitor<TemporalLogic.LTLFormula> visitor = new LTLVisitorImpl();
        CharStream stream = CharStreams.fromString(formula);
        net.maswag.falcaun.LTLLexer lexer = new net.maswag.falcaun.LTLLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        net.maswag.falcaun.LTLParser parser = new net.maswag.falcaun.LTLParser(tokens);
        ParseTree tree = parser.expr();
        return visitor.visit(tree);
    }
}
