package net.maswag;

import net.maswag.TemporalLogic.LTLFormula;
import net.maswag.TemporalLogic.STLCost;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

public class LTLFactory {
    /**
     * <p>parse an LTL formula</p>
     *
     * @param formula a {@link String} object.
     * @return a {@link STLCost} object.
     */
    public LTLFormula parse(String formula) {
        net.maswag.LTLVisitor<LTLFormula> visitor = new LTLVisitorImpl();
        CharStream stream = CharStreams.fromString(formula);
        net.maswag.LTLLexer lexer = new net.maswag.LTLLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        net.maswag.LTLParser parser = new net.maswag.LTLParser(tokens);
        ParseTree tree = parser.expr();
        return visitor.visit(tree);
    }
}
