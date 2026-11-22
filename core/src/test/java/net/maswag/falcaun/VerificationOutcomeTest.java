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

        assertFalse(verifier.run());
        assertEquals(properties, verifier.getCexProperty());
        // The reported output is the output of the SUL
        Word<String> cexInput = verifier.getCexAbstractInput().get(0);
        assertEquals(simulate(cexInput), verifier.getCexOutput().get(0));
        assertEquals(mapper.mapInput(cexInput).asList(), verifier.getCexConcreteInput().get(0).getSignalValues());
    }

    @Test
    void equivalenceTestingExhausted() {
        // The running sum never reaches 100 within LENGTH steps
        NumericSULVerifier verifier = verifier(List.of(parse("[] (output(0) < 100.0)")));
        verifier.addCornerCaseEQOracle(LENGTH, LENGTH / 2);

        assertTrue(verifier.run());
        assertTrue(verifier.getCexProperty().isEmpty());
    }

    @Test
    void timeout() {
        List<TemporalLogic.STLCost> properties = List.of(parse("[] (output(0) < 3.0)"));
        NumericSULVerifier verifier = verifier(properties);
        // Equivalence testing is skipped because the timeout (0 seconds) is reached before the first equivalence query.
        verifier.setTimeout(0);
        verifier.addCornerCaseEQOracle(LENGTH, LENGTH / 2);

        assertTrue(verifier.run());
        assertTrue(verifier.getCexProperty().isEmpty());
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

        assertFalse(verifier.run());
        assertEquals(properties.subList(0, 2), verifier.getCexProperty());
        System.out.println("SUL executions: " + verifier.getSutExecutionCount()
                + ", for equivalence testing: " + verifier.getEqSutExecutionCount());
        assertEquals(73, verifier.getSutExecutionCount());
        assertEquals(48, verifier.getEqSutExecutionCount());
    }
}
