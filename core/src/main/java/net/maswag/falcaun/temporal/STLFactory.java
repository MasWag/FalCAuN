package net.maswag.falcaun.temporal;

import org.antlr.v4.runtime.BaseErrorListener;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.RecognitionException;
import org.antlr.v4.runtime.Recognizer;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;

import net.maswag.falcaun.abstraction.OutputMapper;
import net.maswag.falcaun.temporal.TemporalLogic.STLCost;
import net.maswag.falcaun.temporal.parser.STLLexer;
import net.maswag.falcaun.temporal.parser.STLParser;
import net.maswag.falcaun.temporal.parser.STLVisitor;

import java.util.List;
import java.util.Map;

public class STLFactory {
    /**
     * Rejects malformed STL formulas, e.g., unsupported comparison operators such as {@literal <} or {@literal >=},
     * instead of letting ANTLR silently recover from the syntax error.
     */
    private static final BaseErrorListener THROWING_ERROR_LISTENER = new BaseErrorListener() {
        @Override
        public void syntaxError(Recognizer<?, ?> recognizer, Object offendingSymbol,
                                int line, int charPositionInLine, String msg, RecognitionException e) {
            throw new IllegalArgumentException(
                    String.format("Invalid STL formula at %d:%d: %s", line, charPositionInLine, msg), e);
        }
    };

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
     * <p>parse an STL formula using an output mapper object</p>
     *
     * @param stlFormula   a {@link java.lang.String} object.
     * @param inputMapper  a {@link java.util.List} object.
     * @param outputMapper a {@link net.maswag.falcaun.abstraction.OutputMapper} object.
     * @return a {@link TemporalLogic.STLCost} object.
     */
    public TemporalLogic.STLCost parse(String stlFormula,
                                       List<Map<Character, Double>> inputMapper,
                                       OutputMapper outputMapper) {
        return this.parse(stlFormula, inputMapper, outputMapper.getOutputMapper(), outputMapper.getLargest());
    }

    /**
     * <p>parse an STL formula without setting the mapper</p>
     *
     * @param formula a {@link java.lang.String} object.
     * @return a {@link TemporalLogic.STLCost} object.
     * @throws IllegalArgumentException if the formula is syntactically invalid
     */
    public TemporalLogic.STLCost parse(String formula) {
        STLVisitor<TemporalLogic.STLCost> visitor = new STLVisitorImpl();
        return parseImpl(formula, visitor);
    }

    private static TemporalLogic.STLCost parseImpl(String formula,
                                                   STLVisitor<TemporalLogic.STLCost> visitor) {
        CharStream stream = CharStreams.fromString(formula);
        STLLexer lexer = new STLLexer(stream);
        lexer.removeErrorListeners();
        lexer.addErrorListener(THROWING_ERROR_LISTENER);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        STLParser parser = new STLParser(tokens);
        parser.removeErrorListeners();
        parser.addErrorListener(THROWING_ERROR_LISTENER);
        ParseTree tree = parser.expr();
        // The grammar does not require EOF after expr; reject trailing input instead of ignoring it.
        Token trailing = parser.getCurrentToken();
        if (trailing.getType() != Token.EOF) {
            throw new IllegalArgumentException(String.format(
                    "Invalid STL formula at %d:%d: unexpected trailing input '%s'",
                    trailing.getLine(), trailing.getCharPositionInLine(), trailing.getText()));
        }
        return visitor.visit(tree);
    }
}
