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
    public Double apply(Word<List<Double>> signal) {
        return getRoSI(signal).upperBound;
    }

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
     * @return a {@link org.group_mmm.STLCost.RoSI} object.
     */
    public abstract RoSI getRoSI(Word<List<Double>> signal);

    class RoSI {
        Double lowerBound;
        Double upperBound;

        RoSI(double lowerBound, double upperBound) {
            this.lowerBound = lowerBound;
            this.upperBound = upperBound;
        }

        RoSI(double value) {
            this.lowerBound = value;
            this.upperBound = value;
        }

        RoSI max(RoSI element) {
            return new RoSI(
                    Double.max(lowerBound, element.lowerBound),
                    Double.max(upperBound, element.upperBound));
        }

        RoSI assignMax(RoSI element) {
            lowerBound = Double.max(lowerBound, element.lowerBound);
            upperBound = Double.max(upperBound, element.upperBound);
            return this;
        }

        RoSI min(RoSI element) {
            return new RoSI(
                    Double.min(lowerBound, element.lowerBound),
                    Double.min(upperBound, element.upperBound));
        }

        /**
         * Destructive min
         */
        RoSI assignMin(RoSI element) {
            lowerBound = Double.min(lowerBound, element.lowerBound);
            upperBound = Double.min(upperBound, element.upperBound);
            return this;
        }

        RoSI negate() {
            return new RoSI(-upperBound, -lowerBound);
        }

        RoSI assignNegate() {
            double tmp = lowerBound;
            lowerBound = -upperBound;
            upperBound = -tmp;
            return this;
        }
    }

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
