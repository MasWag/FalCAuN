package net.maswag.falcaun.parser;

import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.tree.ParseTree;
import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import net.maswag.falcaun.parser.STLFactory;
import net.maswag.falcaun.parser.STLOutputAtomic;
import net.maswag.falcaun.parser.STLVisitorImpl;
import net.maswag.falcaun.parser.STLLexer;
import net.maswag.falcaun.parser.STLVisitor;
import net.maswag.falcaun.parser.TemporalAnd.STLAnd;
import net.maswag.falcaun.parser.TemporalEventually.STLEventually;
import net.maswag.falcaun.parser.TemporalGlobally.STLGlobally;
import net.maswag.falcaun.parser.TemporalImply.STLImply;
import net.maswag.falcaun.parser.TemporalLogic.STLCost;
import net.maswag.falcaun.parser.TemporalNext.STLNext;
import net.maswag.falcaun.parser.TemporalNot.STLNot;
import net.maswag.falcaun.parser.TemporalOr.STLOr;
import net.maswag.falcaun.parser.TemporalRelease.STLRelease;
import net.maswag.falcaun.parser.TemporalSub.STLSub;
import net.maswag.falcaun.parser.TemporalUntil.STLUntil;

import java.util.*;

import static net.maswag.falcaun.parser.STLAbstractAtomic.Operation.*;
import static org.junit.jupiter.api.Assertions.*;

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
                    "signal(0) < 10.0",
                    "signal(1) > 4.2",
                    "signal(1) == -20",
                    "(signal(0) < 10.0) || (signal(1) == 2.2)",
                    "(signal(0) < 10.0) || (signal(1) == 2.2 && signal(0) > 10.0)",
                    "(signal(0) < -1.0) -> (signal(1) == 2.2)",
                    "X (signal(1) == -20)",
                    "[] (signal(1) == -20)",
                    "<> (signal(1) == -20)",
                    "alw_[0,2] (signal(1) == -20)",
                    "ev_[10,20] (signal(1) == -20)",
                    "[] ((signal(2) != 4 && X (signal(2) == 4)) -> []_[0,1] (signal(2) == 4))",
                    "[] ((signal(2) == 3) -> signal(0) > 20)", // S2
                    "alw((signal(1) < 4770) || (X (signal(1) > 600)))", // S5
                    "(signal(0) > 100) U (signal(1) < 20)", // Until
                    "(signal(0) > 100) R (signal(1) < 20)", // Release
                    "(!(signal(0) > 0)) || (alw_[0,5] signal(1) < 15)"
            );
            expectedList = Arrays.asList(
                    new STLOutputAtomic(0, lt, 10.0),
                    new STLOutputAtomic(1, gt, 4.2),
                    new STLOutputAtomic(1, eq, -20),
                    new STLOr(new STLOutputAtomic(0, lt, 10.0),
                            new STLOutputAtomic(1, eq, 2.2)),
                    new STLOr(new STLOutputAtomic(0, lt, 10.0),
                            new STLAnd(new STLOutputAtomic(1, eq, 2.2),
                                    new STLOutputAtomic(0, gt, 10.0))),
                    new STLImply(new STLOutputAtomic(0, lt, -1.0),
                            new STLOutputAtomic(1, eq, 2.2)),
                    new STLNext(new STLOutputAtomic(1, eq, -20), true),
                    new STLGlobally(new STLOutputAtomic(1, eq, -20)),
                    new STLEventually(new STLOutputAtomic(1, eq, -20)),
                    new STLSub(
                            new STLGlobally(new STLOutputAtomic(1, eq, -20)), 0, 2),
                    new STLSub(
                            new STLEventually(new STLOutputAtomic(1, eq, -20)), 10, 20),
                    new STLGlobally(new STLImply(
                            new STLAnd(
                                    new STLOutputAtomic(2, ne, 4.0),
                                    new STLNext(new STLOutputAtomic(2, eq, 4.0), false)),
                            new STLSub(new STLGlobally(new STLOutputAtomic(2, eq, 4.0)), 0, 1))),
                    // S2
                    new STLGlobally(new STLImply(new STLOutputAtomic(2, STLOutputAtomic.Operation.eq, 3),
                            new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 20))),
                    // S5
                    new STLGlobally(
                            new STLOr(
                                    new STLOutputAtomic(1, STLOutputAtomic.Operation.lt, 4770),
                                    new STLNext(new STLOutputAtomic(1, STLOutputAtomic.Operation.gt, 600.0), true))),
                    new STLUntil(new STLOutputAtomic(0, gt, 100), new STLOutputAtomic(1, lt, 20)),
                    new STLRelease(new STLOutputAtomic(0, gt, 100), new STLOutputAtomic(1, lt, 20)),
                    new STLOr(new STLNot(new STLOutputAtomic(0, gt, 0)), new STLSub(new STLGlobally(new STLOutputAtomic(1, lt, 15)), 0, 5))
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
}
