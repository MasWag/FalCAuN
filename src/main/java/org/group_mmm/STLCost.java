package org.group_mmm;

import net.automatalib.words.Word;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

abstract class STLCost implements Function<Word<ArrayList<Double>>, Double> {
    boolean nonTemporal;
    Set<String> atomicStrings;

    Set<String> getAtomicStrings() {
        return atomicStrings;
    }

    static STLCost parseSTL(String stlFormula,
                            List<Map<Character, Double>> outputMapper,
                            List<Character> largest) {
        org.group_mmm.STLVisitor visitor = new STLVisitorImpl(outputMapper, largest);
        return parseSTLImpl(stlFormula, visitor);
    }

    protected abstract Set<String> getAllAPs();

    protected abstract void constructAtomicStrings();

    abstract String toAbstractString();

    static STLCost parseSTL(String stlFormula) {
        org.group_mmm.STLVisitor visitor = new STLVisitorImpl();
        return parseSTLImpl(stlFormula, visitor);
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
