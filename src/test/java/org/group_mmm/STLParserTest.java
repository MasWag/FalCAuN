package org.group_mmm;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.junit.jupiter.api.Test;

import java.util.AbstractMap;
import java.util.Arrays;
import java.util.List;

import static org.group_mmm.STLAtomic.Operation.*;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;


class STLParserTest {
    @Test
    void expr() {
        List<String> inputs = Arrays.asList(
                "signal(0) < 10.0",
                "signal(10) > 4.2",
                "signal(1) == -20",
                "(signal(0) < 10.0) || (signal(10) == 2.2)",
                "(signal(0) < -1.0) -> (signal(10) == 2.2)",
                "X (signal(1) == -20)",
                "[] (signal(1) == -20)",
                "<> (signal(1) == -20)",
                "alw_[0,2] (signal(1) == -20)",
                "ev_[10,20] (signal(1) == -20)"
        );
        List<STLCost> expectedList = Arrays.asList(
                new STLAtomic(0, lt, 10.0),
                new STLAtomic(10, gt, 4.2),
                new STLAtomic(1, eq, -20),
                new STLOr(new STLAtomic(0, lt, 10.0),
                        new STLAtomic(10, eq, 2.2)),
                new STLImply(new STLAtomic(0, lt, -1.0),
                        new STLAtomic(10, eq, 2.2)),
                new STLNext(new STLAtomic(1, eq, -20), true),
                new STLGlobal(new STLAtomic(1, eq, -20)),
                new STLEventually(new STLAtomic(1, eq, -20)),
                new STLSub(
                        new STLGlobal(new STLAtomic(1, eq, -20)), 0, 2),
                new STLSub(
                        new STLEventually(new STLAtomic(1, eq, -20)), 10, 20)
        );

        assert inputs.size() == expectedList.size();

        for (int i = 0; i < inputs.size(); i++) {
            CharStream stream = CharStreams.fromString(inputs.get(i));
            org.group_mmm.STLLexer lexer = new org.group_mmm.STLLexer(stream);
            CommonTokenStream tokens = new CommonTokenStream(lexer);
            org.group_mmm.STLParser parser = new org.group_mmm.STLParser(tokens);
            ParseTree tree = parser.expr();
            org.group_mmm.STLVisitor visitor = new STLVisitorImpl();

            assertEquals(expectedList.get(i).toString(), visitor.visit(tree).toString());
        }
    }

    @Test
    void atomic() {
        List<String> inputs = Arrays.asList(
                "signal(0) < 10.0",
                "signal(10) > 4.2",
                "signal(1) == -20");
        List<STLAtomic> expectedList = Arrays.asList(
                new STLAtomic(0, lt, 10.0),
                new STLAtomic(10, gt, 4.2),
                new STLAtomic(1, eq, -20));

        assert inputs.size() == expectedList.size();

        for (int i = 0; i < inputs.size(); i++) {
            CharStream stream = CharStreams.fromString(inputs.get(i));
            org.group_mmm.STLLexer lexer = new org.group_mmm.STLLexer(stream);
            CommonTokenStream tokens = new CommonTokenStream(lexer);
            org.group_mmm.STLParser parser = new org.group_mmm.STLParser(tokens);
            ParseTree tree = parser.atomic();
            org.group_mmm.STLVisitor visitor = new STLVisitorImpl();

            assertEquals(expectedList.get(i).toString(), visitor.visit(tree).toString());
        }
    }

    @Test
    void interval() {
        List<String> inputs = Arrays.asList(
                "[10,20]",
                "(10,20]");
        List<AbstractMap.SimpleEntry<Integer, Integer>> expecteds = Arrays.asList(
                new AbstractMap.SimpleEntry<>(10, 20),
                null);

        assert inputs.size() == expecteds.size();

        for (int i = 0; i < inputs.size(); i++) {
            CharStream stream = CharStreams.fromString(inputs.get(i));
            org.group_mmm.STLLexer lexer = new org.group_mmm.STLLexer(stream);
            CommonTokenStream tokens = new CommonTokenStream(lexer);
            org.group_mmm.STLParser parser = new org.group_mmm.STLParser(tokens);
            ParseTree tree = parser.interval();

            org.group_mmm.STLVisitor visitor = new STLVisitorImpl();

            if (expecteds.get(i) == null) {
                assertThrows(NullPointerException.class, () -> visitor.visit(tree));
            } else {
                assertEquals(expecteds.get(i), visitor.visit(tree));
            }
        }
    }
}
