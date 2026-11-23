package net.maswag.falcaun.verification;

import de.learnlib.driver.simulator.MealySimulatorSUL;
import de.learnlib.oracle.MembershipOracle;
import de.learnlib.oracle.membership.SULOracle;
import de.learnlib.sul.SUL;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.alphabet.impl.ArrayAlphabet;
import net.automatalib.automaton.transducer.impl.CompactMealy;
import net.automatalib.util.automaton.builder.AutomatonBuilders;
import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;
import net.maswag.falcaun.oracle.EvaluationCountable;
import net.maswag.falcaun.oracle.StopDisprovedEQOracle;
import net.maswag.falcaun.temporal.StaticSTLList;
import net.maswag.falcaun.temporal.STLAbstractAtomic;
import net.maswag.falcaun.temporal.STLOutputAtomic;
import net.maswag.falcaun.temporal.TemporalLogic;
import net.maswag.falcaun.temporal.TemporalGlobally.STLGlobally;
import net.maswag.falcaun.temporal.TemporalImply.STLImply;
import net.maswag.falcaun.temporal.TemporalLogic.STLCost;
import net.maswag.falcaun.temporal.TemporalNext.STLNext;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.util.*;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;
class BlackBoxVerifierTest {
    /**
     * Exposes the protected {@link StaticSTLList#notifyFalsifiedProperty(List)} so that it can be verified from this package.
     */
    static class SpiedStaticSTLList<I> extends StaticSTLList<I> {
        SpiedStaticSTLList(Collection<? extends TemporalLogic<I>> properties) {
            super(properties);
        }

        @Override
        public void notifyFalsifiedProperty(List<Integer> falsifiedIndices) {
            super.notifyFalsifiedProperty(falsifiedIndices);
        }
    }

    private final Alphabet<String> inputAlphabet = new ArrayAlphabet<>("a");
    SpiedStaticSTLList<List<Double>> stlList;
    private BlackBoxVerifier<List<Double>> verifier;
    private List<STLCost> properties;
    private List<STLOutputAtomic> events;
    private List<STLCost> falsifiedProperties;
    MembershipOracle.MealyMembershipOracle<String, String> memOracle;
    SUL<String, String> sul;

    @BeforeEach
    void setUp() {
        events = new ArrayList<>();
        events.add(new STLOutputAtomic(0, STLAbstractAtomic.Operation.lt, 1.0));
        events.add(new STLOutputAtomic(0, STLAbstractAtomic.Operation.gt, 1.0));
        events.get(0).setAtomic(Collections.singletonList(Collections.singletonMap('a', 1.0)), Collections.singletonList('b'));
        events.get(1).setAtomic(Collections.singletonList(Collections.singletonMap('a', 1.0)), Collections.singletonList('b'));

        properties = Arrays.asList(
                new STLNext(new STLNext(new STLNext(events.get(1), true), true), true),
                events.get(0),
                new STLGlobally(new STLImply(events.get(1), new STLNext(events.get(0), true))),
                new STLNext(new STLNext(events.get(1), true), true));
        falsifiedProperties = new ArrayList<>();
        falsifiedProperties.add(properties.get(3));
        CompactMealy<String, String> mealy = new CompactMealy<>(inputAlphabet);
        mealy = AutomatonBuilders.forMealy(mealy).
                withInitial("q0").
                from("q0").
                on("a").withOutput("a").to("q1").
                from("q1").
                on("a").withOutput("b").to("q0").
                create();
        sul = new MealySimulatorSUL<>(mealy);
        memOracle = new SULOracle<>(sul);
        stlList = spy(new SpiedStaticSTLList<>(properties));
        stlList.setMemOracle(memOracle);
        verifier = new BlackBoxVerifier<>(memOracle, sul, stlList, inputAlphabet);
        stlList.stream();
    }

    @Test
    void run() {
        VerificationResult<List<Double>> result = verifier.run();
        assertFalse(result.allTargetsFalsified());
        // No equivalence oracle is added, so equivalence testing is exhausted after model checking
        assertEquals(VerificationResult.TerminationReason.EQUIVALENCE_TESTING_EXHAUSTED, result.reason());
        assertTrue(result.failure().isEmpty());
        assertEquals(2, result.statistics().hypothesisStates());
        assertTrue(result.statistics().learningRounds() >= 1);
        assertTrue(result.statistics().sutExecutions().isEmpty());
    }

    @Test
    void notifyFalsifiedProperty() {
        doCallRealMethod().when(stlList).notifyFalsifiedProperty(Arrays.asList(0, 1, 2, 3));
        verifier.run();
        verify(stlList, times(0)).notifyFalsifiedProperty(Collections.singletonList(0));
        verify(stlList, times(0)).notifyFalsifiedProperty(Collections.singletonList(1));
        verify(stlList, times(0)).notifyFalsifiedProperty(Collections.singletonList(2));
        verify(stlList, times(1)).notifyFalsifiedProperty(Collections.singletonList(3));
        verify(stlList, times(0)).notifyFalsifiedProperty(Arrays.asList(0, 1, 2, 3));
    }

    @Test
    void falsifiedAndUnresolved() {
        VerificationResult<List<Double>> result = verifier.run();
        assertEquals(falsifiedProperties, result.falsified());
        assertEquals(properties.subList(0, 3), result.unresolved());
    }

    @Test
    void counterexample() {
        VerificationResult<List<Double>> result = verifier.run();
        assertEquals(1, result.counterexamples().size());
        VerificationResult.Counterexample<List<Double>> cex = result.counterexamples().get(0);
        assertEquals(properties.get(3), cex.property());
        assertEquals(Word.fromSymbols("a", "a", "a"), cex.abstractInput());
        assertEquals(Word.fromSymbols("a", "b", "a"), cex.hypothesisOutput());
        // The output is observed by executing the SUL
        assertEquals(Word.fromSymbols("a", "b", "a"), cex.sutOutput());
        assertTrue(cex.confirmed());
        assertEquals(cex.hypothesisOutput(), cex.witness().computeOutput(cex.abstractInput()));
    }

    /**
     * Run the verifier with an SUL that behaves as the Mealy machine during the learning and as {@code switchedSUL}
     * afterward, i.e., when the counterexamples are validated.
     */
    private VerificationResult<List<Double>> runWithSwitchedSUL(List<STLCost> targets,
                                                                Function<Word<String>, Word<String>> switchedSUL) {
        boolean[] switched = {false};
        MembershipOracle.MealyMembershipOracle<String, String> switchingOracle = queries -> {
            for (var query : queries) {
                if (switched[0]) {
                    query.answer(switchedSUL.apply(query.getInput()).suffix(query.getSuffix().size()));
                } else {
                    query.answer(memOracle.answerQuery(query.getPrefix(), query.getSuffix()));
                }
            }
        };
        // The properties are reset just before the counterexamples are validated, so we switch the SUL there.
        StaticSTLList<List<Double>> list = new StaticSTLList<>(targets) {
            @Override
            public void reset() {
                switched[0] = true;
            }
        };
        list.setMemOracle(switchingOracle);
        return new BlackBoxVerifier<>(switchingOracle, sul, list, inputAlphabet).run();
    }

    /**
     * The SUL outputs "a" first and then always "b".
     */
    private static Word<String> firstAThenB(Word<String> input) {
        WordBuilder<String> output = new WordBuilder<>();
        for (int i = 0; i < input.size(); i++) {
            output.add(i == 0 ? "a" : "b");
        }
        return output.toWord();
    }

    /**
     * A counterexample is not confirmed if the observed trace of the SUL does not violate the specification.
     */
    @Test
    void unconfirmedCounterexample() {
        // The SUL outputs "a b b" for the counterexample, which satisfies the property
        VerificationResult<List<Double>> result =
                runWithSwitchedSUL(Collections.singletonList(properties.get(3)), BlackBoxVerifierTest::firstAThenB);
        assertEquals(1, result.counterexamples().size());
        VerificationResult.Counterexample<List<Double>> cex = result.counterexamples().get(0);
        assertFalse(cex.confirmed());
        assertFalse(cex.agreesWithHypothesis());
        assertEquals(Word.fromSymbols("a", "b", "a"), cex.hypothesisOutput());
        assertEquals(Word.fromSymbols("a", "b", "b"), cex.sutOutput());
        assertTrue(result.falsified().isEmpty());
        assertTrue(result.confirmedCounterexamples().isEmpty());
        assertEquals(List.of(properties.get(3)), result.unresolved());
        assertFalse(result.allTargetsFalsified());
        // The loop terminated because the property was falsified during the learning
        assertEquals(VerificationResult.TerminationReason.ALL_TARGETS_FALSIFIED, result.reason());
    }

    /**
     * A counterexample is confirmed if the observed trace of the SUL violates the specification, even if the observed
     * output differs from the output of the learned Mealy machine.
     */
    @Test
    void confirmedCounterexampleWithDifferentOutput() {
        // The SUL outputs "a a a" for the counterexample, which differs from "a b a" but still violates the property
        VerificationResult<List<Double>> result = runWithSwitchedSUL(Collections.singletonList(properties.get(3)),
                input -> Word.fromList(Collections.nCopies(input.size(), "a")));
        assertEquals(1, result.counterexamples().size());
        VerificationResult.Counterexample<List<Double>> cex = result.counterexamples().get(0);
        assertEquals(Word.fromSymbols("a", "b", "a"), cex.hypothesisOutput());
        assertEquals(Word.fromSymbols("a", "a", "a"), cex.sutOutput());
        assertFalse(cex.agreesWithHypothesis());
        assertTrue(cex.confirmed());
        assertEquals(List.of(properties.get(3)), result.falsified());
        assertTrue(result.unresolved().isEmpty());
        assertTrue(result.allTargetsFalsified());
    }

    /**
     * The counterexamples confirmed before a failure of the SUL execution are still reported.
     */
    @Test
    void executionFailureDuringValidationKeepsConfirmedCounterexamples() {
        // X X X X (output(0) > 1.0) is violated by the output "a b a b a" for the input "a a a a a"
        STLCost fifthOutput = new STLNext(new STLNext(new STLNext(new STLNext(events.get(1), true), true), true), true);
        List<STLCost> targets = List.of(properties.get(3), fifthOutput);
        // The SUL fails for the counterexample of the second property
        VerificationResult<List<Double>> result = runWithSwitchedSUL(targets, input -> {
            if (input.size() >= 5) {
                throw new de.learnlib.exception.SULException(new IllegalStateException("failure"));
            }
            return memOracle.answerQuery(input);
        });
        assertEquals(VerificationResult.TerminationReason.EXECUTION_FAILURE, result.reason());
        assertTrue(result.failure().isPresent());
        assertEquals(List.of(properties.get(3)), result.falsified());
        assertEquals(List.of(fifthOutput), result.unresolved());
        assertEquals(2, result.targetCount());
        assertFalse(result.allTargetsFalsified());
    }

    /**
     * The targets given only as LTL formulas are not reported as falsified.
     */
    @Test
    void ltlOnlyTargetsAreNotReportedAsFalsified() {
        // The property holds for the Mealy machine, so equivalence testing is exhausted
        StopDisprovedEQOracle.StaticLTLList<List<Double>> ltlList =
                new StopDisprovedEQOracle.StaticLTLList<>(List.of("[] ((output == \"a\") || (output == \"b\"))"));
        ltlList.setMemOracle(memOracle);
        BlackBoxVerifier<List<Double>> ltlVerifier = new BlackBoxVerifier<>(memOracle, sul, ltlList, inputAlphabet);
        ltlVerifier.addRandomWordEQOracle(1, 5, 10, new Random(0), 1);
        VerificationResult<List<Double>> result = ltlVerifier.run();
        assertEquals(VerificationResult.TerminationReason.EQUIVALENCE_TESTING_EXHAUSTED, result.reason());
        assertEquals(1, result.targetCount());
        assertTrue(result.falsified().isEmpty());
        assertFalse(result.allTargetsFalsified());

        // The same for the timeout
        StopDisprovedEQOracle.StaticLTLList<List<Double>> timeoutList =
                new StopDisprovedEQOracle.StaticLTLList<>(List.of("[] ((output == \"a\") || (output == \"b\"))"));
        timeoutList.setMemOracle(memOracle);
        BlackBoxVerifier<List<Double>> timeoutVerifier = new BlackBoxVerifier<>(memOracle, sul, timeoutList, inputAlphabet);
        timeoutVerifier.setTimeout(0);
        timeoutVerifier.addRandomWordEQOracle(1, 5, 10, new Random(0), 1);
        VerificationResult<List<Double>> timeoutResult = timeoutVerifier.run();
        assertEquals(VerificationResult.TerminationReason.TIMEOUT, timeoutResult.reason());
        assertFalse(timeoutResult.allTargetsFalsified());
    }

    /**
     * The corner-case equivalence oracle is not used once all the targets are disproved.
     * This is ensured by {@link StopDisprovedEQOracle}, which wraps the equivalence oracles added to the verifier.
     */
    @Test
    void cornerCaseOracleStopsAfterAllTargetsDisproved() {
        StaticSTLList<List<Double>> list = new StaticSTLList<>(Collections.singletonList(properties.get(3)));
        list.setMemOracle(memOracle);
        BlackBoxVerifier<List<Double>> cornerVerifier = new BlackBoxVerifier<>(memOracle, sul, list, inputAlphabet);
        EvaluationCountable cornerCase = cornerVerifier.addCornerCaseEQOracle(4, 2);
        VerificationResult<List<Double>> result = cornerVerifier.run();
        assertEquals(VerificationResult.TerminationReason.ALL_TARGETS_FALSIFIED, result.reason());
        assertEquals(List.of(properties.get(3)), result.falsified());
        // Without StopDisprovedEQOracle, the corner cases would be evaluated after the property is disproved
        assertEquals(0, cornerCase.getEvaluateCount());
    }

    @Test
    void executionFailure() {
        MembershipOracle.MealyMembershipOracle<String, String> failingOracle = queries -> {
            throw new de.learnlib.exception.SULException(new IllegalStateException("failure"));
        };
        StaticSTLList<List<Double>> list = new StaticSTLList<>(properties);
        list.setMemOracle(failingOracle);
        VerificationResult<List<Double>> result = new BlackBoxVerifier<>(failingOracle, sul, list, inputAlphabet).run();
        assertEquals(VerificationResult.TerminationReason.EXECUTION_FAILURE, result.reason());
        assertTrue(result.failure().isPresent());
        assertTrue(result.counterexamples().isEmpty());
        assertEquals(properties, result.unresolved());
        assertFalse(result.allTargetsFalsified());
    }

    @Test
    void writeETFLearnedMealy() {
        verifier.run();
        String expected = "begin state\n" +
                "id:id\n" +
                "end state\n" +
                "begin edge\n" +
                "input:input\n" +
                "output:output\n" +
                "end edge\n" +
                "begin init\n" +
                "0\n" +
                "end init\n" +
                "begin sort id\n" +
                "\"s0\"\n" +
                "\"s1\"\n" +
                "end sort\n" +
                "begin trans\n" +
                "0/1 0 0\n" +
                "1/0 0 1\n" +
                "end trans\n" +
                "begin sort input\n" +
                "\"a\"\n" +
                "end sort\n" +
                "begin sort output\n" +
                "\"a\"\n" +
                "\"b\"\n" +
                "end sort\n";
        ByteArrayOutputStream stream = new ByteArrayOutputStream();
        verifier.writeETFLearnedMealy(stream);
        assertEquals(expected, stream.toString());
    }
}
