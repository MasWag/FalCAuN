package net.maswag.falcaun;

import net.automatalib.word.Word;
import net.maswag.falcaun.parser.STLFactory;
import net.maswag.falcaun.parser.TemporalLogic;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.*;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.*;

/**
 * End-to-end tests of the verification outcomes of {@link NumericSULVerifier} with a deterministic SUL.
 */
class VerificationOutcomeTest {
    private static final int LENGTH = 4;
    /**
     * Abstract input "a", "b", and "c" are mapped to 0.0, 1.0, and 2.0, respectively.
     */
    private static final List<Map<Character, Double>> INPUT_MAPPER =
            Collections.singletonList(Map.of('a', 0.0, 'b', 1.0, 'c', 2.0));
    private static final List<Map<Character, Double>> OUTPUT_MAPPER =
            Collections.singletonList(Map.of('a', 3.0, 'b', 100.0));
    private static final List<Character> LARGEST = Collections.singletonList('c');
    private CountingNumericSUL sul;
    private NumericSULMapper mapper;

    private static TemporalLogic.STLCost parse(String formula) {
        return new STLFactory().parse(formula, INPUT_MAPPER, OUTPUT_MAPPER, LARGEST);
    }

    @BeforeEach
    void setUp() {
        sul = new CountingNumericSUL();
        mapper = new NumericSULMapper(INPUT_MAPPER, LARGEST, OUTPUT_MAPPER, new SimpleSignalMapper());
    }

    private NumericSULVerifier verifier(List<TemporalLogic.STLCost> properties) {
        return new NumericSULVerifier(sul, 1.0, new StaticSTLList<>(properties), mapper);
    }

    /**
     * Run the SUL from scratch and returns the abstract output.
     */
    private Word<String> simulate(Word<String> abstractInput) throws Exception {
        CountingNumericSUL fresh = new CountingNumericSUL();
        IOSignal<List<Double>> signal = fresh.execute(mapper.mapInput(abstractInput));
        return Word.fromList(signal.stream().map(mapper::mapOutput).collect(Collectors.toList()));
    }

    @Test
    void allTargetsFalsified() throws Exception {
        List<TemporalLogic.STLCost> properties = List.of(parse("[] (output(0) < 3.0)"));
        NumericSULVerifier verifier = verifier(properties);
        verifier.addCornerCaseEQOracle(LENGTH, LENGTH / 2);

        VerificationResult<List<Double>> result = verifier.run();
        assertEquals(VerificationResult.TerminationReason.ALL_TARGETS_FALSIFIED, result.reason());
        assertTrue(result.allTargetsFalsified());
        assertEquals(properties, result.falsified());
        assertTrue(result.unresolved().isEmpty());
        // The reported output is the output of the SUL
        VerificationResult.Counterexample<List<Double>> cex = result.counterexamples().get(0);
        assertTrue(cex.confirmed());
        assertEquals(simulate(cex.abstractInput()), cex.sutOutput());
        assertEquals(mapper.mapInput(cex.abstractInput()).asList(), verifier.concreteInput(cex).getSignalValues());
        // The statistics of the SUL executions are reported
        assertEquals(sul.getExecutionCount(), result.statistics().sutExecutions().orElseThrow());
        assertEquals(verifier.getEqEvaluationCount(), result.statistics().eqEvaluations().orElseThrow());
        assertTrue(result.statistics().simulationTimeSeconds().isPresent());
    }

    @Test
    void equivalenceTestingExhausted() {
        // The running sum never reaches 100 within LENGTH steps
        NumericSULVerifier verifier = verifier(List.of(parse("[] (output(0) < 100.0)")));
        verifier.addCornerCaseEQOracle(LENGTH, LENGTH / 2);

        VerificationResult<List<Double>> result = verifier.run();
        assertEquals(VerificationResult.TerminationReason.EQUIVALENCE_TESTING_EXHAUSTED, result.reason());
        // Exhausted equivalence testing does not prove the specification
        assertEquals(verifier.getProperties().getSTLProperties(), result.unresolved());
        assertTrue(result.counterexamples().isEmpty());
        assertFalse(result.allTargetsFalsified());
    }

    @Test
    void timeout() {
        List<TemporalLogic.STLCost> properties = List.of(parse("[] (output(0) < 3.0)"));
        NumericSULVerifier verifier = verifier(properties);
        // Equivalence testing is skipped because the timeout (0 seconds) is reached before the first equivalence query.
        verifier.setTimeout(0);
        verifier.addCornerCaseEQOracle(LENGTH, LENGTH / 2);

        VerificationResult<List<Double>> result = verifier.run();
        assertEquals(VerificationResult.TerminationReason.TIMEOUT, result.reason());
        assertEquals(properties, result.unresolved());
        assertTrue(result.falsified().isEmpty());
    }

    @Test
    void executionFailure() {
        NumericSULVerifier verifier = verifier(List.of(parse("[] (output(0) < 3.0)")));
        verifier.addCornerCaseEQOracle(LENGTH, LENGTH / 2);
        sul.setFailAtStep(2);

        VerificationResult<List<Double>> result = verifier.run();
        assertEquals(VerificationResult.TerminationReason.EXECUTION_FAILURE, result.reason());
        assertTrue(result.failure().isPresent());
        assertTrue(result.counterexamples().isEmpty());
        // The session of the failed execution is finalized
        assertEquals("post", sul.getEvents().get(sul.getEvents().size() - 1));
    }

    /**
     * A representative deterministic run with corner-case and robustness-guided equivalence testing.
     * The numbers of SUL executions are the reference for the refactoring of the caches.
     */
    @Test
    void executionCounts() {
        List<TemporalLogic.STLCost> properties = List.of(
                parse("[] (output(0) < 3.0)"),
                parse("[] (output(0) < 5.0)"),
                parse("[] (output(0) < 100.0)"));
        NumericSULVerifier verifier = verifier(properties);
        verifier.addCornerCaseEQOracle(LENGTH, LENGTH / 2);
        verifier.addHillClimbingEQOracleAll(LENGTH, new Random(0), 30, 5, 5, false);

        VerificationResult<List<Double>> result = verifier.run();
        assertEquals(properties.subList(0, 2), result.falsified());
        assertEquals(properties.subList(2, 3), result.unresolved());
        assertEquals(VerificationResult.TerminationReason.EQUIVALENCE_TESTING_EXHAUSTED, result.reason());
        System.out.println("SUL executions: " + verifier.getSutExecutionCount()
                + ", for equivalence testing: " + verifier.getEqEvaluationCount());
        assertEquals(73, verifier.getSutExecutionCount());
        assertEquals(48, verifier.getEqEvaluationCount());
        // The 4 re-executions are of the words executed by the membership oracle (or by the corner-case equivalence
        // oracle) and then requested by the robustness-based equivalence oracles.
        assertEquals(69, new HashSet<>(sul.getExecutedInputs()).size());
    }
}
