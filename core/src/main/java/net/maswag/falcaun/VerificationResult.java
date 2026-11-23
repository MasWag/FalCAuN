package net.maswag.falcaun;

import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.word.Word;
import net.maswag.falcaun.parser.TemporalLogic;

import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalDouble;
import java.util.OptionalInt;

/**
 * The result of black-box checking by {@link BlackBoxVerifier} or {@link NumericSULVerifier}.
 * <p>
 * A target specification is <em>falsified</em> only if a counterexample is confirmed by the observation of the SUL
 * (see {@link Counterexample#confirmed()}). The other target specifications are <em>unresolved</em>.
 * <p>
 * The counterexamples and the unresolved specifications are reported only for the target specifications represented
 * as {@link TemporalLogic} formulas. A target specification given only as an LTL formula (e.g., by
 * {@link StopDisprovedEQOracle.StaticLTLList}) is counted in {@code targetCount} but appears in neither list, so
 * {@link #allTargetsFalsified()} is conservatively {@code false} for it.
 * Notice that an unresolved specification is not proved to be satisfied by the SUL: black-box checking is a testing
 * method and cannot prove the absence of counterexamples.
 *
 * @param counterexamples the counterexample candidates found on the learned Mealy machine, including the ones not
 *                        confirmed by the SUL. At most one candidate is reported for each target specification.
 * @param unresolved      the target specifications without a confirmed counterexample
 * @param targetCount     the number of the target specifications, including the ones given only as LTL formulas
 * @param reason          the reason why black-box checking terminated
 * @param statistics      the statistics of black-box checking
 * @param failure         the cause of the termination if {@code reason} is {@link TerminationReason#EXECUTION_FAILURE}.
 *                        The counterexamples confirmed before the failure are still reported.
 * @param <I>             the type of the input at each step of the target specifications
 */
public record VerificationResult<I>(List<Counterexample<I>> counterexamples,
                                    List<TemporalLogic<I>> unresolved,
                                    int targetCount,
                                    TerminationReason reason,
                                    Statistics statistics,
                                    Optional<Throwable> failure) {
    public VerificationResult {
        counterexamples = List.copyOf(counterexamples);
        unresolved = List.copyOf(unresolved);
        Objects.requireNonNull(reason);
        Objects.requireNonNull(statistics);
        Objects.requireNonNull(failure);
    }

    /**
     * The reason why black-box checking terminated.
     */
    public enum TerminationReason {
        /**
         * Equivalence testing stopped because all the target specifications were falsified.
         */
        ALL_TARGETS_FALSIFIED,
        /**
         * The equivalence oracles did not find any further counterexample.
         * This is <em>not</em> a proof that the SUL satisfies the unresolved specifications.
         */
        EQUIVALENCE_TESTING_EXHAUSTED,
        /**
         * At least one equivalence oracle was skipped because of the timeout.
         * The timeout is checked only before each invocation of an equivalence oracle (see {@link TimeoutEQOracle}),
         * so the elapsed time can exceed the timeout.
         */
        TIMEOUT,
        /**
         * The execution of the SUL failed. The cause is in {@link VerificationResult#failure()}.
         * The counterexamples confirmed before the failure are still reported.
         */
        EXECUTION_FAILURE
    }

    /**
     * A counterexample candidate of a target specification.
     * <p>
     * The candidate is found by model checking of the learned Mealy machine. Its input is executed on the SUL, and
     * the specification is checked on the observed abstract trace, i.e., the pair of {@code abstractInput} and
     * {@code sutOutput}, by the same model checker. The candidate is <em>confirmed</em> if the observed trace violates
     * the specification. The observed output may differ from the output of the learned Mealy machine even if the
     * candidate is confirmed (see {@link #agreesWithHypothesis()}).
     *
     * @param property         the target specification violated by the learned Mealy machine
     * @param abstractInput    the abstract input word
     * @param hypothesisOutput the abstract output word of the learned Mealy machine
     * @param sutOutput        the abstract output word observed by executing the SUL
     * @param confirmed        whether the observed trace of the SUL violates {@code property}
     * @param witness          the Mealy machine witnessing the violation by the learned Mealy machine
     * @param <I>              the type of the input at each step of the specification
     */
    public record Counterexample<I>(TemporalLogic<I> property,
                                    Word<String> abstractInput,
                                    Word<String> hypothesisOutput,
                                    Word<String> sutOutput,
                                    boolean confirmed,
                                    MealyMachine<?, String, ?, String> witness) {
        /**
         * @return {@code true} if and only if the SUL produced the same output as the learned Mealy machine.
         * A disagreement means that the learned Mealy machine is not yet accurate for the input.
         */
        public boolean agreesWithHypothesis() {
            return sutOutput.equals(hypothesisOutput);
        }
    }

    /**
     * Statistics of black-box checking.
     *
     * @param learningRounds        the number of the learning rounds, i.e., the hypotheses constructed by the learner
     * @param hypothesisStates      the number of the states of the final learned Mealy machine (0 if not available)
     * @param sutExecutions         the number of the executions of the SUL if available
     * @param eqEvaluations         the number of the evaluations of input words by the equivalence oracles if
     *                              available. This is not necessarily the number of the SUL executions because an
     *                              evaluation may be answered by a cache.
     * @param simulationTimeSeconds the time spent for the executions of the SUL if available
     */
    public record Statistics(int learningRounds,
                             int hypothesisStates,
                             OptionalInt sutExecutions,
                             OptionalInt eqEvaluations,
                             OptionalDouble simulationTimeSeconds) {
        /**
         * Statistics without the information on the SUL executions.
         */
        public Statistics(int learningRounds, int hypothesisStates) {
            this(learningRounds, hypothesisStates, OptionalInt.empty(), OptionalInt.empty(), OptionalDouble.empty());
        }
    }

    /**
     * @return the counterexamples confirmed by the SUL
     */
    public List<Counterexample<I>> confirmedCounterexamples() {
        return counterexamples.stream().filter(Counterexample::confirmed).toList();
    }

    /**
     * @return the target specifications falsified by a confirmed counterexample
     */
    public List<TemporalLogic<I>> falsified() {
        return confirmedCounterexamples().stream().map(Counterexample::property).toList();
    }

    /**
     * @return {@code true} if and only if all the target specifications are falsified by confirmed counterexamples.
     * This is conservatively {@code false} if some target specifications are given only as LTL formulas.
     */
    public boolean allTargetsFalsified() {
        return reason != TerminationReason.EXECUTION_FAILURE && unresolved.isEmpty() && falsified().size() == targetCount;
    }

    /**
     * @return a copy of this result with the given statistics
     */
    public VerificationResult<I> withStatistics(Statistics statistics) {
        return new VerificationResult<>(counterexamples, unresolved, targetCount, reason, statistics, failure);
    }
}
