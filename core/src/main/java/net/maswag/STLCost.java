package net.maswag;

import lombok.Getter;
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
public abstract class STLCost implements Function<IOSignal, Double> {
    @Getter
    boolean nonTemporal;
    @Getter
    Set<String> atomicStrings;

    /**
     * <p>parseSTL.</p>
     *
     * @param stlFormula a {@link java.lang.String} object.
     * @param outputMapper a {@link java.util.List} object.
     * @param largest a {@link java.util.List} object.
     * @return a {@link net.maswag.STLCost} object.
     */
    static public STLCost parseSTL(String stlFormula,
                                   List<Map<Character, Double>> inputMapper,
                                   List<Map<Character, Double>> outputMapper,
                                   List<Character> largest) {
        net.maswag.STLVisitor<STLCost> visitor = new STLVisitorImpl(inputMapper, outputMapper, largest);
        return parseSTLImpl(stlFormula, visitor);
    }

    static STLCost parseSTL(String stlFormula) {
        net.maswag.STLVisitor<STLCost> visitor = new STLVisitorImpl();
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

    public String toLTLString() {
        return this.toAbstractString();
    }

    private static STLCost parseSTLImpl(String stlFormula,
                                        net.maswag.STLVisitor<STLCost> visitor) {
        CharStream stream = CharStreams.fromString(stlFormula);
        net.maswag.STLLexer lexer = new net.maswag.STLLexer(stream);
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        net.maswag.STLParser parser = new net.maswag.STLParser(tokens);
        ParseTree tree = parser.expr();
        return visitor.visit(tree);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Double apply(IOSignal signal) {
        return getRoSI(signal).getRobustness();
    }

    /**
     * <p>getRoSI.</p>
     *
     * @param signal a {@link net.automatalib.words.Word} object.
     * @return a {@link RoSI} object.
     */
    public abstract RoSI getRoSI(IOSignal signal);

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        STLCost stlCost = (STLCost) o;

        return this.hashCode() == stlCost.hashCode();
    }

    @Override
    public int hashCode() {
        // Hash code is implemented based on the string representation.
        return this.toString().hashCode();
    }
}
