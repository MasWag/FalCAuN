package org.group_mmm;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.util.*;

import static org.group_mmm.STLAtomic.Operation.*;
import static org.group_mmm.STLCost.parseSTL;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;


class STLParserTest {

    @Nested
    class Expr {
        private List<String> inputs;
        private List<STLCost> expectedList;

        @BeforeEach
        void setUp() {
            inputs = Arrays.asList(
                    "signal(0) < 10.0",
                    "signal(1) > 4.2",
                    "signal(1) == -20",
                    "(signal(0) < 10.0) || (signal(1) == 2.2)",
                    "(signal(0) < -1.0) -> (signal(1) == 2.2)",
                    "X (signal(1) == -20)",
                    "[] (signal(1) == -20)",
                    "<> (signal(1) == -20)",
                    "alw_[0,2] (signal(1) == -20)",
                    "ev_[10,20] (signal(1) == -20)",
                    "[] ((signal(2) != 4 && X (signal(2) == 4)) -> []_[0,1] (signal(2) == 4))",
                    "[] ((signal(2) == 3) -> signal(0) > 20)", // S2
                    "alw((signal(1) < 4770) || (X (signal(1) > 600)))" // S5
            );
            expectedList = Arrays.asList(
                    new STLAtomic(0, lt, 10.0),
                    new STLAtomic(1, gt, 4.2),
                    new STLAtomic(1, eq, -20),
                    new STLOr(new STLAtomic(0, lt, 10.0),
                            new STLAtomic(1, eq, 2.2)),
                    new STLImply(new STLAtomic(0, lt, -1.0),
                            new STLAtomic(1, eq, 2.2)),
                    new STLNext(new STLAtomic(1, eq, -20), true),
                    new STLGlobal(new STLAtomic(1, eq, -20)),
                    new STLEventually(new STLAtomic(1, eq, -20)),
                    new STLSub(
                            new STLGlobal(new STLAtomic(1, eq, -20)), 0, 2),
                    new STLSub(
                            new STLEventually(new STLAtomic(1, eq, -20)), 10, 20),
                    new STLGlobal(new STLImply(
                            new STLAnd(
                                    new STLAtomic(2, ne, 4.0),
                                    new STLNext(new STLAtomic(2, eq, 4.0), false)),
                            new STLSub(new STLGlobal(new STLAtomic(2, eq, 4.0)), 0, 1))),
                    // S2
                    new STLGlobal(new STLImply(new STLAtomic(2, STLAtomic.Operation.eq, 3),
                            new STLAtomic(0, STLAtomic.Operation.gt, 20))),
                    // S5
                    new STLGlobal(
                            new STLOr(
                                    new STLAtomic(1, STLAtomic.Operation.lt, 4770),
                                    new STLNext(new STLAtomic(1, STLAtomic.Operation.gt, 600.0), true)))
            );

            assert inputs.size() == expectedList.size();
        }

        @Test
        void withoutMapper() {
            for (int i = 0; i < inputs.size(); i++) {
                STLCost result = parseSTL(inputs.get(i));
                assertThrows(NullPointerException.class, result::toAbstractString);
                assertEquals(expectedList.get(i).toString(), result.toString());
            }
        }

        @Test
        void withMapper() {
            Map<Character, Double> velocityMap = new HashMap<>();
            velocityMap.put('a', -1.0);
            velocityMap.put('b', 10.0);

            Map<Character, Double> rotationMap = new HashMap<>();
            rotationMap.put('a', -20.0);
            rotationMap.put('b', 2.2);
            rotationMap.put('c', 4.2);

            Map<Character, Double> gearMap = new HashMap<>();

            List<Map<Character, Double>> outputMapper = Arrays.asList(velocityMap, rotationMap, gearMap);
            List<Character> largest = Arrays.asList('c', 'd', 'a');

            for (int i = 0; i < inputs.size(); i++) {
                STLCost result = parseSTL(inputs.get(i), outputMapper, largest);
                Assertions.assertThat(result.toAbstractString()).contains("output == ");
                assertEquals(expectedList.get(i).toString(), result.toString());
            }
        }
    }

    @Test
    void atomic() {
        List<String> inputs = Arrays.asList(
                "signal(0) < 10.0",
                "signal(10) > 4.2",
                "signal(2) != -0.2",
                "signal(1) == -20");
        List<STLAtomic> expectedList = Arrays.asList(
                new STLAtomic(0, lt, 10.0),
                new STLAtomic(10, gt, 4.2),
                new STLAtomic(2, ne, -0.2),
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
