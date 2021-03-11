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

import static org.group_mmm.STLAbstractAtomic.Operation.*;
import static org.group_mmm.STLCost.parseSTL;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;


class STLParserTest {

    @Test
    void atomic() {
        List<String> inputs = Arrays.asList(
                "signal(0) < 10.0",
                "signal(10) > 4.2",
                "signal(2) != -0.2",
                "signal(1) == -20");
        List<STLOutputAtomic> expectedList = Arrays.asList(
                new STLOutputAtomic(0, lt, 10.0),
                new STLOutputAtomic(10, gt, 4.2),
                new STLOutputAtomic(2, ne, -0.2),
                new STLOutputAtomic(1, eq, -20));

        for (int i = 0; i < inputs.size(); i++) {
            CharStream stream = CharStreams.fromString(inputs.get(i));
            org.group_mmm.STLLexer lexer = new org.group_mmm.STLLexer(stream);
            CommonTokenStream tokens = new CommonTokenStream(lexer);
            org.group_mmm.STLParser parser = new org.group_mmm.STLParser(tokens);
            ParseTree tree = parser.atomic();
            org.group_mmm.STLVisitor<STLCost> visitor = new STLVisitorImpl();

            assertEquals(expectedList.get(i).toString(), visitor.visit(tree).toString());
        }
    }

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
                    "alw((signal(1) < 4770) || (X (signal(1) > 600)))", // S5
                    "(signal(0) > 100) U (signal(1) < 20)" // Until
            );
            expectedList = Arrays.asList(
                    new STLOutputAtomic(0, lt, 10.0),
                    new STLOutputAtomic(1, gt, 4.2),
                    new STLOutputAtomic(1, eq, -20),
                    new STLOr(new STLOutputAtomic(0, lt, 10.0),
                            new STLOutputAtomic(1, eq, 2.2)),
                    new STLImply(new STLOutputAtomic(0, lt, -1.0),
                            new STLOutputAtomic(1, eq, 2.2)),
                    new STLNext(new STLOutputAtomic(1, eq, -20), true),
                    new STLGlobal(new STLOutputAtomic(1, eq, -20)),
                    new STLEventually(new STLOutputAtomic(1, eq, -20)),
                    new STLSub(
                            new STLGlobal(new STLOutputAtomic(1, eq, -20)), 0, 2),
                    new STLSub(
                            new STLEventually(new STLOutputAtomic(1, eq, -20)), 10, 20),
                    new STLGlobal(new STLImply(
                            new STLAnd(
                                    new STLOutputAtomic(2, ne, 4.0),
                                    new STLNext(new STLOutputAtomic(2, eq, 4.0), false)),
                            new STLSub(new STLGlobal(new STLOutputAtomic(2, eq, 4.0)), 0, 1))),
                    // S2
                    new STLGlobal(new STLImply(new STLOutputAtomic(2, STLOutputAtomic.Operation.eq, 3),
                            new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 20))),
                    // S5
                    new STLGlobal(
                            new STLOr(
                                    new STLOutputAtomic(1, STLOutputAtomic.Operation.lt, 4770),
                                    new STLNext(new STLOutputAtomic(1, STLOutputAtomic.Operation.gt, 600.0), true))),
                    new STLUntil(new STLOutputAtomic(0, gt, 100), new STLOutputAtomic(1, lt, 20))
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

            List<Map<Character, Double>> inputMapper = Collections.emptyList();
            List<Map<Character, Double>> outputMapper = Arrays.asList(velocityMap, rotationMap, gearMap);
            List<Character> largest = Arrays.asList('c', 'd', 'a');

            for (int i = 0; i < inputs.size(); i++) {
                STLCost result = parseSTL(inputs.get(i), inputMapper, outputMapper, largest);
                Assertions.assertThat(result.toAbstractString()).contains("output == ");
                assertEquals(expectedList.get(i).toString(), result.toString());
            }
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
