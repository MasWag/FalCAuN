package net.maswag.falcaun;

import de.learnlib.query.DefaultQuery;
import net.automatalib.word.Word;
import net.maswag.falcaun.parser.STLFactory;
import net.maswag.falcaun.parser.TemporalLogic;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.util.*;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Regression tests for the interaction of membership queries, robustness-based cost oracles, and their caches.
 * <p>
 * Each test checks both the answers and the number of actual SUL executions.
 */
class NumericMembershipOracleCachingTest {
    private static final double EPS = 1e-9;

    /**
     * Abstract input "a", "b", and "c" are mapped to 0.0, 1.0, and 2.5, respectively.
     * We avoid the values on the thresholds of the output mappers so that the tests do not depend on the comparison semantics.
     */
    private static final List<Map<Character, Double>> INPUT_MAPPER =
            Collections.singletonList(Map.of('a', 0.0, 'b', 1.0, 'c', 2.5));

    private static Word<String> word(String... symbols) {
        return Word.fromSymbols(symbols);
    }

    /**
     * The construction of the membership oracle and the cost oracles as in {@link NumericSULVerifier}.
     */
    private static final class Fixture {
        final NumericMembershipOracle memOracle;

        Fixture(NumericSUL sul, SignalDiscretizer discretizer) {
            this.memOracle = new NumericMembershipOracle(sul, discretizer);
        }

        RobustnessOracle register(Function<IOSignal<List<Double>>, Double> costFunc) {
            return memOracle.registerCostFunction(costFunc);
        }

        double cost(RobustnessOracle oracle, Word<String> input) {
            return oracle.processQueryWithCost(new DefaultQuery<>(input));
        }

        int evaluateCount(RobustnessOracle oracle) {
            return oracle.getEvaluateCount();
        }
    }

    @Nested
    class Discrete {
        private CountingNumericSUL sul;
        private Fixture fixture;
        private TemporalLogic.STLCost below3;
        private TemporalLogic.STLCost below4;

        @BeforeEach
        void setUp() {
            sul = new CountingNumericSUL();
            List<Map<Character, Double>> outputMapper = Collections.singletonList(Map.of('a', 3.0));
            List<Character> largest = Collections.singletonList('b');
            NumericSULMapper mapper = new NumericSULMapper(INPUT_MAPPER, largest, outputMapper, new SimpleSignalMapper());
            fixture = new Fixture(sul, mapper);
            below3 = new STLFactory().parse("[] (output(0) < 3.0)", INPUT_MAPPER, outputMapper, largest);
            below4 = new STLFactory().parse("[] (output(0) < 4.0)", INPUT_MAPPER, outputMapper, largest);
        }

        @Test
        void repeatedQueries() {
            Word<String> input = word("b", "c", "a");
            Word<String> first = fixture.memOracle.answerQuery(input);
            Word<String> second = fixture.memOracle.answerQuery(input);
            // The running sums are 1, 3.5, 3.5
            assertEquals(word("a", "b", "b"), first);
            assertEquals(first, second);
            assertEquals(1, sul.getExecutionCount());
        }

        @Test
        void prefixAndSuffixQueries() {
            fixture.memOracle.answerQuery(word("b", "c", "a"));
            assertEquals(1, sul.getExecutionCount());
            // A prefix of an executed word is answered from the cache
            assertEquals(word("a", "b"), fixture.memOracle.answerQuery(word("b", "c")));
            // Only the output for the suffix is returned
            assertEquals(word("b", "b"), fixture.memOracle.answerQuery(word("b"), word("c", "a")));
            assertEquals(1, sul.getExecutionCount());
            // An extension of an executed word requires a new execution
            assertEquals(word("a", "b", "b", "b"), fixture.memOracle.answerQuery(word("b", "c", "a", "a")));
            assertEquals(2, sul.getExecutionCount());
            assertEquals(List.of(List.of(1.0), List.of(2.5), List.of(0.0), List.of(0.0)), sul.getExecutedInputs().get(1));
        }

        @Test
        void robustnessIsPrefixWise() {
            RobustnessOracle oracle = fixture.register(below3);
            // The running sums are 1, 3.5, 3.5
            assertEquals(3.0 - 3.5, fixture.cost(oracle, word("b", "c", "a")), EPS);
            assertEquals(1, sul.getExecutionCount());
            // The robustness of the prefixes is cached
            assertEquals(3.0 - 1.0, fixture.cost(oracle, word("b")), EPS);
            assertEquals(1, sul.getExecutionCount());
            assertEquals(1, fixture.evaluateCount(oracle));
        }

        @Test
        void costQueryAnswersTheAbstractOutput() {
            RobustnessOracle oracle = fixture.register(below3);
            DefaultQuery<String, Word<String>> query = new DefaultQuery<>(word("b"), word("c", "a"));
            oracle.processQueryWithCost(query);
            assertEquals(word("b", "b"), query.getOutput());
            // The abstract output is shared with the membership oracle
            assertEquals(word("a", "b", "b"), fixture.memOracle.answerQuery(word("b", "c", "a")));
            assertEquals(1, sul.getExecutionCount());
        }

        @Test
        void multipleCostFunctionsShareExecutions() {
            RobustnessOracle oracle3 = fixture.register(below3);
            RobustnessOracle oracle4 = fixture.register(below4);
            assertEquals(3.0 - 3.5, fixture.cost(oracle3, word("b", "c", "a")), EPS);
            assertEquals(1, sul.getExecutionCount());
            // The robustness for the other cost function is computed from the same execution
            assertEquals(4.0 - 3.5, fixture.cost(oracle4, word("b", "c", "a")), EPS);
            assertEquals(4.0 - 1.0, fixture.cost(oracle4, word("b")), EPS);
            assertEquals(1, sul.getExecutionCount());
            assertEquals(1, fixture.evaluateCount(oracle3));
            assertEquals(0, fixture.evaluateCount(oracle4));
            // A new word executed by the second oracle is also shared
            assertEquals(4.0 - 5.0, fixture.cost(oracle4, word("c", "c")), EPS);
            assertEquals(3.0 - 5.0, fixture.cost(oracle3, word("c", "c")), EPS);
            assertEquals(2, sul.getExecutionCount());
        }

        @Test
        void costQueryAfterMembershipQuery() {
            RobustnessOracle oracle = fixture.register(below3);
            fixture.memOracle.answerQuery(word("b", "c", "a"));
            assertEquals(1, sul.getExecutionCount());
            // The robustness for the registered cost functions is computed for every execution, including the
            // executions for membership queries. (Before the consolidation of the caches, this required another
            // execution because only the executions by the cost oracles computed the robustness.)
            assertEquals(3.0 - 3.5, fixture.cost(oracle, word("b", "c", "a")), EPS);
            assertEquals(1, sul.getExecutionCount());
            assertEquals(0, fixture.evaluateCount(oracle));
        }

        @Test
        void costFunctionRegisteredAfterEvaluation() {
            RobustnessOracle oracle3 = fixture.register(below3);
            assertEquals(3.0 - 3.5, fixture.cost(oracle3, word("b", "c", "a")), EPS);
            assertEquals(1, sul.getExecutionCount());
            // The robustness for a cost function registered later is not available without an execution:
            // a cached abstract output is not sufficient to compute the robustness.
            RobustnessOracle oracle4 = fixture.register(below4);
            assertEquals(4.0 - 3.5, fixture.cost(oracle4, word("b", "c", "a")), EPS);
            assertEquals(2, sul.getExecutionCount());
            assertEquals(1, fixture.evaluateCount(oracle4));
            // After that, both robustness values are cached
            assertEquals(3.0 - 3.5, fixture.cost(oracle3, word("b", "c", "a")), EPS);
            assertEquals(4.0 - 3.5, fixture.cost(oracle4, word("b", "c", "a")), EPS);
            assertEquals(2, sul.getExecutionCount());
        }

        @Test
        void infiniteRobustnessIsReevaluated() {
            RobustnessOracle oracle = fixture.register(signal -> Double.POSITIVE_INFINITY);
            assertEquals(Double.POSITIVE_INFINITY, fixture.cost(oracle, word("b", "c")));
            assertEquals(Double.POSITIVE_INFINITY, fixture.cost(oracle, word("b", "c")));
            assertEquals(2, sul.getExecutionCount());
            assertEquals(2, fixture.evaluateCount(oracle));
        }

        @Test
        void executionFailureIsReported() {
            sul.setFailAtStep(1);
            Exception e = assertThrows(RuntimeException.class, () -> fixture.memOracle.answerQuery(word("b", "c")));
            assertTrue(e.getMessage().contains("[b, c]") || e.getMessage().contains("b c"), e.getMessage());
            // Nothing is cached for a failed execution
            sul.setFailAtStep(-1);
            assertEquals(word("a", "b"), fixture.memOracle.answerQuery(word("b", "c")));
        }
    }

    @Nested
    class Continuous {
        private static final double SIGNAL_STEP = 1.0;
        private CountingContinuousNumericSUL sul;
        private Fixture fixture;
        private TemporalLogic.STLCost derivedBelow15;
        private TemporalLogic.STLCost outputBelow3;

        @BeforeEach
        void setUp() {
            sul = new CountingContinuousNumericSUL(SIGNAL_STEP);
            // The derived signal is the maximum of the continuous output since the previous sampling point.
            Function<IOSignalPiece<List<Double>>, Double> maxSinceLast = piece -> {
                if (piece instanceof ExtendedIOSignalPiece<List<Double>> extended) {
                    return extended.getPreviousOutputSignals().stream().mapToDouble(v -> v.get(0)).max().orElseThrow();
                }
                return piece.getOutputSignal().get(0);
            };
            List<Map<Character, Double>> outputMapper = Arrays.asList(Map.of('a', 3.0), Map.of('a', 15.0));
            List<Character> largest = Arrays.asList('b', 'b');
            NumericSULMapper mapper = new NumericSULMapper(INPUT_MAPPER, largest, outputMapper,
                    new SimpleSignalMapper(Collections.singletonList(maxSinceLast)));
            fixture = new Fixture(sul, mapper);
            derivedBelow15 = new STLFactory().parse("[] (output(1) < 15.0)", INPUT_MAPPER, outputMapper, largest);
            outputBelow3 = new STLFactory().parse("[] (output(0) < 3.0)", INPUT_MAPPER, outputMapper, largest);
        }

        @Test
        void derivedSignalUsesContinuousOutput() {
            // The sampled outputs are 1, 3.5, 3.5 and the intermediate samples are 1 + 25 = 26 and 3.5 + 0 = 3.5.
            // Thus, the derived signal is 1, 26, 3.5.
            Word<String> input = word("b", "c", "a");
            assertEquals(word("aa", "bb", "ba"), fixture.memOracle.answerQuery(input));
            assertEquals(1, sul.getExecutionCount());

            RobustnessOracle derived = fixture.register(derivedBelow15);
            RobustnessOracle sampled = fixture.register(outputBelow3);
            assertEquals(15.0 - 26.0, fixture.cost(derived, input), EPS);
            assertEquals(15.0 - 1.0, fixture.cost(derived, word("b")), EPS);
            assertEquals(3.0 - 3.5, fixture.cost(sampled, input), EPS);
            assertEquals(3.0 - 1.0, fixture.cost(sampled, word("b")), EPS);
            // The robustness for "derived" requires an execution, which is shared with "sampled"
            assertEquals(2, sul.getExecutionCount());
        }
    }
}
