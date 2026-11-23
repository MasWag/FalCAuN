package net.maswag.falcaun.temporal;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import net.maswag.falcaun.temporal.parser.STLParser;
import net.maswag.falcaun.temporal.parser.STLLexer;
import net.maswag.falcaun.temporal.parser.STLVisitor;
import net.maswag.falcaun.temporal.TemporalAnd.STLAnd;
import net.maswag.falcaun.temporal.TemporalEventually.STLEventually;
import net.maswag.falcaun.temporal.TemporalGlobally.STLGlobally;
import net.maswag.falcaun.temporal.TemporalImply.STLImply;
import net.maswag.falcaun.temporal.TemporalLogic.STLCost;
import net.maswag.falcaun.temporal.TemporalNext.STLNext;
import net.maswag.falcaun.temporal.TemporalNot.STLNot;
import net.maswag.falcaun.temporal.TemporalOr.STLOr;
import net.maswag.falcaun.temporal.TemporalRelease.STLRelease;
import net.maswag.falcaun.temporal.TemporalSub.STLSub;
import net.maswag.falcaun.temporal.TemporalUntil.STLUntil;

import java.util.*;

import static net.maswag.falcaun.temporal.STLAbstractAtomic.Operation.*;
import static org.junit.jupiter.api.Assertions.*;

class STLParserTest {

    @Test
    void atomic() {
        List<String> inputs = Arrays.asList(
                "signal(0) <= 10.0",
                "signal(10) > 4.2",
                "signal(2) != -0.2",
                "signal(1) == -20");
        List<STLOutputAtomic> expectedList = Arrays.asList(
                new STLOutputAtomic(0, LE, 10.0),
                new STLOutputAtomic(10, GT, 4.2),
                new STLOutputAtomic(2, NE, -0.2),
                new STLOutputAtomic(1, EQ, -20));

        for (int i = 0; i < inputs.size(); i++) {
            CharStream stream = CharStreams.fromString(inputs.get(i));
            STLLexer lexer = new STLLexer(stream);
            CommonTokenStream tokens = new CommonTokenStream(lexer);
            STLParser parser = new STLParser(tokens);
            ParseTree tree = parser.atomic();
            STLVisitor<STLCost> visitor = new STLVisitorImpl();

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
                    "signal(0) <= 10.0",
                    "signal(1) > 4.2",
                    "signal(1) == -20",
                    "(signal(0) <= 10.0) || (signal(1) == 2.2)",
                    "(signal(0) <= 10.0) || (signal(1) == 2.2 && signal(0) > 10.0)",
                    "(signal(0) <= -1.0) -> (signal(1) == 2.2)",
                    "X (signal(1) == -20)",
                    "[] (signal(1) == -20)",
                    "<> (signal(1) == -20)",
                    "alw_[0,2] (signal(1) == -20)",
                    "ev_[10,20] (signal(1) == -20)",
                    "[] ((signal(2) != 4 && X (signal(2) == 4)) -> []_[0,1] (signal(2) == 4))",
                    "[] ((signal(2) == 3) -> signal(0) > 20)", // S2
                    "alw((signal(1) <= 4770) || (X (signal(1) > 600)))", // S5
                    "(signal(0) > 100) U (signal(1) <= 20)", // Until
                    "(signal(0) > 100) R (signal(1) <= 20)", // Release
                    "(!(signal(0) > 0)) || (alw_[0,5] signal(1) <= 15)"
            );
            expectedList = Arrays.asList(
                    new STLOutputAtomic(0, LE, 10.0),
                    new STLOutputAtomic(1, GT, 4.2),
                    new STLOutputAtomic(1, EQ, -20),
                    new STLOr(new STLOutputAtomic(0, LE, 10.0),
                            new STLOutputAtomic(1, EQ, 2.2)),
                    new STLOr(new STLOutputAtomic(0, LE, 10.0),
                            new STLAnd(new STLOutputAtomic(1, EQ, 2.2),
                                    new STLOutputAtomic(0, GT, 10.0))),
                    new STLImply(new STLOutputAtomic(0, LE, -1.0),
                            new STLOutputAtomic(1, EQ, 2.2)),
                    new STLNext(new STLOutputAtomic(1, EQ, -20), true),
                    new STLGlobally(new STLOutputAtomic(1, EQ, -20)),
                    new STLEventually(new STLOutputAtomic(1, EQ, -20)),
                    new STLSub(
                            new STLGlobally(new STLOutputAtomic(1, EQ, -20)), 0, 2),
                    new STLSub(
                            new STLEventually(new STLOutputAtomic(1, EQ, -20)), 10, 20),
                    new STLGlobally(new STLImply(
                            new STLAnd(
                                    new STLOutputAtomic(2, NE, 4.0),
                                    new STLNext(new STLOutputAtomic(2, EQ, 4.0), false)),
                            new STLSub(new STLGlobally(new STLOutputAtomic(2, EQ, 4.0)), 0, 1))),
                    // S2
                    new STLGlobally(new STLImply(new STLOutputAtomic(2, STLOutputAtomic.Operation.EQ, 3),
                            new STLOutputAtomic(0, STLOutputAtomic.Operation.GT, 20))),
                    // S5
                    new STLGlobally(
                            new STLOr(
                                    new STLOutputAtomic(1, STLOutputAtomic.Operation.LE, 4770),
                                    new STLNext(new STLOutputAtomic(1, STLOutputAtomic.Operation.GT, 600.0), true))),
                    new STLUntil(new STLOutputAtomic(0, GT, 100), new STLOutputAtomic(1, LE, 20)),
                    new STLRelease(new STLOutputAtomic(0, GT, 100), new STLOutputAtomic(1, LE, 20)),
                    new STLOr(new STLNot(new STLOutputAtomic(0, GT, 0)), new STLSub(new STLGlobally(new STLOutputAtomic(1, LE, 15)), 0, 5))
            );

            assert inputs.size() == expectedList.size();
        }

        @Test
        void withoutMapper() {
            STLFactory factory = new STLFactory();
            for (int i = 0; i < inputs.size(); i++) {
                STLCost result = factory.parse(inputs.get(i));
                assertFalse(result.isInitialized());
                assertThrows(IllegalStateException.class, result::toAbstractString);
                assertEquals(expectedList.get(i).toString(), result.toString());
            }
        }

        @Test
        void withMapper() {
            STLFactory factory = new STLFactory();
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
                STLCost result = factory.parse(inputs.get(i), inputMapper, outputMapper, largest);
                assertTrue(result.isInitialized());
                Assertions.assertThat(result.toAbstractString()).contains("output == ");
                assertEquals(expectedList.get(i).toString(), result.toString());
            }
        }
    }

    /**
     * Regression tests for #305: {@literal <=} is the non-strict comparison, and {@literal <} and {@literal >=} are rejected.
     */
    @Nested
    class Comparison {
        private final STLFactory factory = new STLFactory();

        @Test
        void leParsesForAllSignalKinds() {
            Map<String, STLAbstractAtomic> expected = Map.of(
                    "input(0) <= 1.5", new STLInputAtomic(0, LE, 1.5),
                    "output(1) <= -2", new STLOutputAtomic(1, LE, -2),
                    "signal(2) <= 3.0", new STLOutputAtomic(2, LE, 3.0),
                    "signal(0)<=4", new STLOutputAtomic(0, LE, 4));
            expected.forEach((formula, atomic) -> {
                STLCost result = factory.parse(formula);
                assertInstanceOf(STLAbstractAtomic.class, result);
                assertEquals(LE, ((STLAbstractAtomic) result).op);
                assertEquals(atomic.toString(), result.toString());
                Assertions.assertThat(result.toString()).contains(" <= ");
            });
        }

        @Test
        void printedFormulaRoundTrips() {
            for (String formula : List.of(
                    "input(0) <= 1.5",
                    "[] (output(0) <= 120)",
                    "(output(0) > 10) U (output(1) <= 4.2)",
                    "<> (output(0) <= 1)")) {
                STLCost parsed = factory.parse(formula);
                STLCost reparsed = factory.parse(parsed.toString());
                assertEquals(parsed.toString(), reparsed.toString());
            }
        }

        @Test
        void eventuallyStillParses() {
            STLCost result = factory.parse("<> (output(0) <= 1)");
            assertInstanceOf(STLEventually.class, result);
            assertEquals(new STLEventually(new STLOutputAtomic(0, LE, 1)).toString(), result.toString());
        }

        @Test
        void unsupportedComparisonsAreRejected() {
            for (String formula : List.of(
                    "signal(0) < 10.0",
                    "signal(0)<10",
                    "input(0) < 1",
                    "output(0) >= 10.0",
                    "output(0)>=10",
                    "[] (output(0) < 1)",
                    "[] (output(0) >= 1)",
                    "(output(0) > 1) && (output(1) < 2)")) {
                assertThrows(IllegalArgumentException.class, () -> factory.parse(formula), formula);
            }
        }

        @Test
        void trailingInputIsRejected() {
            for (String formula : List.of(
                    "output(0) <= 1 output(1) > 2",
                    "output(0) <= 1 )",
                    "(output(0) <= 1) (output(1) <= 2)",
                    "[] (output(0) <= 1) output(1) < 2")) {
                assertThrows(IllegalArgumentException.class, () -> factory.parse(formula), formula);
            }
        }
    }
}
