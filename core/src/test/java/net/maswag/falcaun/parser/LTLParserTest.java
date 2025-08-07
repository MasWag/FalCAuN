package net.maswag.falcaun.parser;

import net.maswag.falcaun.parser.LTLAtomic;
import net.maswag.falcaun.parser.LTLFactory;
import net.maswag.falcaun.parser.TemporalAnd.LTLAnd;
import net.maswag.falcaun.parser.TemporalEventually.LTLEventually;
import net.maswag.falcaun.parser.TemporalGlobally.LTLGlobally;
import net.maswag.falcaun.parser.TemporalImply.LTLImply;
import net.maswag.falcaun.parser.TemporalLogic.LTLFormula;
import net.maswag.falcaun.parser.TemporalNext.LTLNext;
import net.maswag.falcaun.parser.TemporalOr.LTLOr;
import net.maswag.falcaun.parser.TemporalRelease.LTLRelease;
import net.maswag.falcaun.parser.TemporalSub.LTLSub;
import net.maswag.falcaun.parser.TemporalUntil.LTLUntil;

import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

class LTLParserTest {
    LTLFactory factory = new LTLFactory();

    @Test
    void atomic() {
        List<String> inputs = Arrays.asList(
                "input == a", "(input == b)",
                "output == p", "output == q");
        List<LTLAtomic> expectedList = Arrays.asList(
                new LTLAtomic(Optional.of("a"), Optional.empty()),
                new LTLAtomic(Optional.of("b"), Optional.empty()),
                new LTLAtomic(Optional.empty(), Optional.of("p")),
                new LTLAtomic(Optional.empty(), Optional.of("q")));

        for (int i = 0; i < inputs.size(); i++) {
            LTLFormula result = factory.parse(inputs.get(i));

            assertEquals(expectedList.get(i).toString(), result.toString());
        }
    }

    @Test
    void expr() {
        List<String> inputs = Arrays.asList(
                "input == a",
                "output == p",
                "input == a || output == p",
                "input == a -> output == p",
                "input == a && output == p",
                "X (input == a)",
                "[] (output == p)",
                "<> (input == a)",
                "alw_[0,2] (output == p)",
                "ev_[10,20] (input == a)",
                "(input == a) U (output == p)", // Until
                "(input == a) R (output == p)" // Release
        );
        LTLAtomic left = new LTLAtomic(Optional.of("a"), Optional.empty());
        LTLAtomic right = new LTLAtomic(Optional.empty(), Optional.of("p"));
        List<LTLFormula> expectedList = Arrays.asList(
                left, right,
                new LTLOr(left, right),
                new LTLImply(left, right),
                new LTLAnd(left, right),
                new LTLNext(left, true),
                new LTLGlobally(right),
                new LTLEventually(left),
                new LTLSub(new LTLGlobally(right), 0, 2),
                new LTLSub(new LTLEventually(left), 10, 20),
                new LTLUntil(left, right),
                new LTLRelease(left, right)
        );

        assert inputs.size() == expectedList.size();

        for (int i = 0; i < inputs.size(); i++) {
            LTLFormula result = factory.parse(inputs.get(i));
            assertEquals(expectedList.get(i).toString(), result.toString());
        }
    }

    @Test
    void toStringTest() {
        List<String> inputs = Arrays.asList(
                "input == a ",
                "output == p ",
                "input == a  || output == p ",
                "input == a  || input == a ",
                "( input == a  ) -> ( output == p  )",
                "input == a  && output == p ",
                "X ( input == a  )",
                "[] ( output == p  )",
                "<> ( input == a  )",
                " []_[0, 2] ( output == p  )",
                " <>_[10, 20] ( input == a  )",
                "input == a  U output == p ", // Until
                "input == a  R output == p " // Release
        );
        LTLAtomic left = new LTLAtomic(Optional.of("a"), Optional.empty());
        LTLAtomic right = new LTLAtomic(Optional.empty(), Optional.of("p"));
        List<LTLFormula> expectedList = Arrays.asList(
                left, right,
                new LTLOr(left, right),
                new LTLOr(left, left),
                new LTLImply(left, right),
                new LTLAnd(left, right),
                new LTLNext(left, true),
                new LTLGlobally(right),
                new LTLEventually(left),
                new LTLSub(new LTLGlobally(right), 0, 2),
                new LTLSub(new LTLEventually(left), 10, 20),
                new LTLUntil(left, right),
                new LTLRelease(left, right)
        );

        assert inputs.size() == expectedList.size();

        for (String input : inputs) {
            LTLFormula result = factory.parse(input);
            assertEquals(input, result.toString().replaceAll("\"", ""));
        }
    }

    @Test
    void toAbstractStringTest() {
        List<String> inputs = Arrays.asList(
                "input == a ",
                "output == p ",
                "( input == a  ) || ( output == p  )",
                "input == a ",
                "( input == a  ) -> ( output == p  )",
                "( input == a  ) && ( output == p  )",
                "X ( input == a  )",
                "[] ( output == p  )",
                "<> ( input == a  )",
                //" []_[0, 2] ( output == p  )",
                //" <>_[1, 3] ( input == a  )",
                "( input == a  ) U ( output == p  )", // Until
                "( input == a  ) R ( output == p  )" // Release
        );
        LTLAtomic left = new LTLAtomic(Optional.of("a"), Optional.empty());
        LTLAtomic right = new LTLAtomic(Optional.empty(), Optional.of("p"));
        List<LTLFormula> expectedList = Arrays.asList(
                left, right,
                new LTLOr(left, right),
                new LTLOr(left, left),
                new LTLImply(left, right),
                new LTLAnd(left, right),
                new LTLNext(left, true),
                new LTLGlobally(right),
                new LTLEventually(left),
                //new LTLSub(new LTLGlobally(right), 0, 2),
                //new LTLSub(new LTLEventually(left), 10, 20),
                new LTLUntil(left, right),
                new LTLRelease(left, right)
        );

        assert inputs.size() == expectedList.size();

        for (String input : inputs) {
            LTLFormula result = factory.parse(input);
            assertEquals(input, result.toAbstractString().replaceAll("\"", ""));
        }
    }
}
