package net.maswag.falcaun;

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
import net.maswag.falcaun.parser.STLAbstractAtomic;
import net.maswag.falcaun.parser.STLOutputAtomic;
import net.maswag.falcaun.parser.TemporalGlobally.STLGlobally;
import net.maswag.falcaun.parser.TemporalImply.STLImply;
import net.maswag.falcaun.parser.TemporalLogic.STLCost;
import net.maswag.falcaun.parser.TemporalNext.STLNext;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.util.*;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;
class BlackBoxVerifierTest {
    private final Alphabet<String> inputAlphabet = new ArrayAlphabet<>("a");
    StaticSTLList<List<Double>> stlList;
    private BlackBoxVerifier<List<Double>> verifier;
    private List<STLCost> properties;
    private List<STLCost> falsifiedProperties;
    MembershipOracle.MealyMembershipOracle<String, String> memOracle;
    SUL<String, String> sul;

    @BeforeEach
    void setUp() {
        List<STLOutputAtomic> events = new ArrayList<>();
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
        stlList = spy(new StaticSTLList<>(properties));
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
     * A counterexample is not confirmed if the SUL behaves differently from the learned Mealy machine for the input.
     */
    @Test
    void unconfirmedCounterexample() {
        // After the learning, the SUL starts to output "b" after the first step, which differs from the learned model.
        boolean[] switched = {false};
        MembershipOracle.MealyMembershipOracle<String, String> switchingOracle = queries -> {
            for (var query : queries) {
                if (switched[0]) {
                    WordBuilder<String> output = new WordBuilder<>();
                    for (int i = 0; i < query.getInput().size(); i++) {
                        output.add(i == 0 ? "a" : "b");
                    }
                    query.answer(output.toWord().suffix(query.getSuffix().size()));
                } else {
                    query.answer(memOracle.answerQuery(query.getPrefix(), query.getSuffix()));
                }
            }
        };
        // The properties are reset just before the counterexamples are validated, so we switch the SUL there.
        StaticSTLList<List<Double>> list = new StaticSTLList<>(Collections.singletonList(properties.get(3))) {
            @Override
            public void reset() {
                switched[0] = true;
            }
        };
        list.setMemOracle(switchingOracle);
        VerificationResult<List<Double>> result = new BlackBoxVerifier<>(switchingOracle, sul, list, inputAlphabet).run();
        assertEquals(1, result.counterexamples().size());
        VerificationResult.Counterexample<List<Double>> cex = result.counterexamples().get(0);
        assertFalse(cex.confirmed());
        assertEquals(Word.fromSymbols("a", "b", "a"), cex.hypothesisOutput());
        assertEquals(Word.fromSymbols("a", "b", "b"), cex.sutOutput());
        assertTrue(result.falsified().isEmpty());
        assertTrue(result.confirmedCounterexamples().isEmpty());
        assertEquals(List.of(properties.get(3)), result.unresolved());
        assertFalse(result.allTargetsFalsified());
        // The loop terminated because the property was falsified during the learning
        assertEquals(VerificationResult.TerminationReason.ALL_TARGETS_FALSIFIED, result.reason());
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
