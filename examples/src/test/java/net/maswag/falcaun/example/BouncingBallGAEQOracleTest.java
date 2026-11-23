package net.maswag.falcaun.example;

import net.automatalib.word.Word;
import net.maswag.falcaun.temporal.AdaptiveSTLList;
import net.maswag.falcaun.oracle.GASelectionKind;
import net.maswag.falcaun.signal.IOContinuousSignal;
import net.maswag.falcaun.abstraction.InputMapper;
import net.maswag.falcaun.verification.NumericSULVerifier;
import net.maswag.falcaun.abstraction.OutputMapper;
import net.maswag.falcaun.signal.Signal;
import net.maswag.falcaun.abstraction.SignalAdapter;
import net.maswag.falcaun.verification.VerificationResult;
import net.maswag.falcaun.temporal.STLFactory;
import net.maswag.falcaun.temporal.TemporalLogic;
import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Falsification of the BouncingBall model only with the GA-based equivalence oracle.
 */
class BouncingBallGAEQOracleTest {
    private static final double THRESHOLD = 47.0;
    private static final int SIGNAL_LENGTH = 11;

    @Test
    void falsifyWithGA() throws Exception {
        InputMapper inputMapper = InputMapper.make(Collections.singletonList(Arrays.asList(0.0, 2.5)));
        OutputMapper outputMapper = new OutputMapper(Arrays.asList(Arrays.asList(THRESHOLD, null), Collections.singletonList(null)));
        // The ball goes above the threshold only if the wind is applied at the right timings.
        // Neither the constant nor no wind violates this property.
        TemporalLogic.STLCost stl = new STLFactory().parse("G_[5,10] (output(0) < " + THRESHOLD + ")", inputMapper, outputMapper);
        AdaptiveSTLList<List<Double>> properties = new AdaptiveSTLList<>(Collections.singletonList(stl), SIGNAL_LENGTH);

        try (BouncingBallSUL sul = new BouncingBallSUL()) {
            NumericSULVerifier verifier = new NumericSULVerifier(sul, BouncingBallSUL.DEFAULT_SIMULATION_STEP, properties, new SignalAdapter(inputMapper, outputMapper));
            verifier.addGAEQOracleAll(SIGNAL_LENGTH, 5000, GASelectionKind.Tournament, 50, 0.9, 0.01);

            VerificationResult<List<Double>> result = verifier.run();
            assertTrue(result.allTargetsFalsified(), "The property should be falsified");
            assertTrue(verifier.getEqEvaluationCount() > 0, "The GA-based equivalence oracle should be used");
            // Reported for comparing the numbers of the executions before and after changes of the caches
            System.out.println("BouncingBall SUL executions: " + verifier.getSutExecutionCount()
                    + ", for equivalence testing: " + verifier.getEqEvaluationCount());

            // Check the counterexample by simulating it again
            // The counterexample is a prefix that ends when the property is violated
            Signal cex = verifier.concreteInput(result.confirmedCounterexamples().get(0));
            assertTrue(5 < cex.size() && cex.size() <= SIGNAL_LENGTH);
            try (BouncingBallSUL freshSUL = new BouncingBallSUL()) {
                IOContinuousSignal<List<Double>> simulated = freshSUL.execute(Word.fromList(cex.getSignalValues()));
                double maxPosition = simulated.getOutputSignal().subWord(5, cex.size()).stream()
                        .mapToDouble(output -> output.get(0)).max().orElseThrow();
                assertTrue(maxPosition >= THRESHOLD, "The counterexample should reach " + THRESHOLD + " but the maximum is " + maxPosition);
            }
        }
    }
}
