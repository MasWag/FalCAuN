package org.group_mmm;

import net.automatalib.words.Word;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * <p>Abstract STLCost class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public abstract class STLCost implements Function<Word<List<Double>>, Double> {
    boolean nonTemporal;
    Set<String> atomicStrings;

    Set<String> getAtomicStrings() {
        return atomicStrings;
    }

    /** {@inheritDoc} */
    @Override
    public Double apply(Word<List<Double>> signal) { return getRoSI(signal).getRobustness(); }

    /**
     * <p>parseSTL.</p>
     *
     * @param stlFormula a {@link java.lang.String} object.
     * @param outputMapper a {@link java.util.List} object.
     * @param largest a {@link java.util.List} object.
     * @return a {@link org.group_mmm.STLCost} object.
     */
    static public STLCost parseSTL(String stlFormula,
                                   List<Map<Character, Double>> outputMapper,
                                   List<Character> largest) {
        org.group_mmm.STLVisitor visitor = new STLVisitorImpl(outputMapper, largest);
        return parseSTLImpl(stlFormula, visitor);
    }

    /**
     * <p>getAllAPs.</p>
     *
     * @return a {@link java.util.Set} object.
     */
    protected abstract Set<String> getAllAPs();

    /**
     * <p>constructAtomicStrings.</p>
     */
    protected abstract void constructAtomicStrings();

    /**
     * <p>toAbstractString.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public abstract String toAbstractString();

    static STLCost parseSTL(String stlFormula) {
        org.group_mmm.STLVisitor visitor = new STLVisitorImpl();
        return parseSTLImpl(stlFormula, visitor);
    }

    /**
     * <p>getRoSI.</p>
     *
     * @param signal a {@link net.automatalib.words.Word} object.
     * @return a {@link RoSI} object.
     */
    public abstract RoSI getRoSI(Word<List<Double>> signal);

    private static STLCost parseSTLImpl(String stlFormula,
                                        org.group_mmm.STLVisitor visitor) {
        CharStream stream = CharStreams.fromString(stlFormula);
        org.group_mmm.STLLexer lexer = new org.group_mmm.STLLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        org.group_mmm.STLParser parser = new org.group_mmm.STLParser(tokens);
        ParseTree tree = parser.expr();
        return (STLCost) visitor.visit(tree);
    }

    boolean isNonTemporal() {
        return nonTemporal;
    }
}
