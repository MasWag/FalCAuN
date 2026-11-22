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
 * Notice that an unresolved specification is not proved to be satisfied by the SUL: black-box checking is a testing
 * method and cannot prove the absence of counterexamples.
 *
 * @param counterexamples the counterexample candidates found on the learned Mealy machine, including the ones not
 *                        confirmed by the SUL. At most one candidate is reported for each target specification.
 * @param unresolved      the target specifications without a confirmed counterexample
 * @param reason          the reason why black-box checking terminated
 * @param statistics      the statistics of black-box checking
 * @param failure         the cause of the termination if {@code reason} is {@link TerminationReason#EXECUTION_FAILURE}
 * @param <I>             the type of the input at each step of the target specifications
 */
public record VerificationResult<I>(List<Counterexample<I>> counterexamples,
                                    List<TemporalLogic<I>> unresolved,
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
         */
        EXECUTION_FAILURE
    }

    /**
     * A counterexample of a target specification.
     * <p>
     * The counterexample is found by model checking of the learned Mealy machine. It is <em>confirmed</em> if the
     * output of the SUL for the input is the same as the output of the learned Mealy machine. In that case, the
     * observation of the SUL violates the specification as the learned Mealy machine does.
     *
     * @param property         the violated target specification
     * @param abstractInput    the abstract input word
     * @param hypothesisOutput the abstract output word of the learned Mealy machine
     * @param sutOutput        the abstract output word observed by executing the SUL
     * @param witness          the Mealy machine witnessing the violation, found by the model checker
     * @param <I>              the type of the input at each step of the specification
     */
    public record Counterexample<I>(TemporalLogic<I> property,
                                    Word<String> abstractInput,
                                    Word<String> hypothesisOutput,
                                    Word<String> sutOutput,
                                    MealyMachine<?, String, ?, String> witness) {
        /**
         * @return {@code true} if and only if the observation of the SUL confirms the counterexample.
         */
        public boolean confirmed() {
            return sutOutput.equals(hypothesisOutput);
        }
    }

    /**
     * Statistics of black-box checking.
     *
     * @param learningRounds        the number of the learning rounds, i.e., the hypotheses constructed by the learner
     * @param hypothesisStates      the number of the states of the final learned Mealy machine (0 if not available)
     * @param sutExecutions         the number of the executions of the SUL if available
     * @param eqSutExecutions       the number of the executions of the SUL by the equivalence oracles if available
     * @param simulationTimeSeconds the time spent for the executions of the SUL if available
     */
    public record Statistics(int learningRounds,
                             int hypothesisStates,
                             OptionalInt sutExecutions,
                             OptionalInt eqSutExecutions,
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
     * @return {@code true} if and only if all the target specifications are falsified by confirmed counterexamples
     */
    public boolean allTargetsFalsified() {
        return unresolved.isEmpty() && reason != TerminationReason.EXECUTION_FAILURE;
    }

    /**
     * @return a copy of this result with the given statistics
     */
    public VerificationResult<I> withStatistics(Statistics statistics) {
        return new VerificationResult<>(counterexamples, unresolved, reason, statistics, failure);
    }
}
