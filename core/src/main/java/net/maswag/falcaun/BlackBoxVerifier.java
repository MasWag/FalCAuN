package net.maswag.falcaun;

import de.learnlib.acex.AcexAnalyzers;
import de.learnlib.exception.SULException;
import de.learnlib.algorithm.LearningAlgorithm;
import de.learnlib.algorithm.ttt.mealy.TTTLearnerMealy;
import de.learnlib.oracle.EquivalenceOracle;
import de.learnlib.oracle.MembershipOracle;
import de.learnlib.oracle.PropertyOracle;
import de.learnlib.oracle.equivalence.*;
import de.learnlib.oracle.equivalence.mealy.RandomWalkEQOracle;
import de.learnlib.sul.SUL;
import de.learnlib.util.MealyExperiment;
import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.automaton.transducer.impl.CompactMealy;
import net.automatalib.modelchecker.ltsmin.monitor.LTSminMonitorIOBuilder;
import net.automatalib.modelchecking.ModelChecker;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.serialization.etf.writer.Mealy2ETFWriterIO;
import net.automatalib.visualization.Visualization;
import net.automatalib.word.Word;
import net.maswag.falcaun.VerificationResult.Counterexample;
import net.maswag.falcaun.VerificationResult.Statistics;
import net.maswag.falcaun.VerificationResult.TerminationReason;
import net.maswag.falcaun.parser.TemporalLogic;

import java.io.IOException;
import java.io.OutputStream;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

import static net.automatalib.util.automaton.Automata.stateCover;

/**
 * Verifies a black-box system against specified properties using various equivalence oracles and model checking techniques.
 * <p>
 * This class provides a comprehensive framework for verifying the behavior of a black-box system by comparing it against a set of Signal Temporal Logic (STL) properties.
 * It utilizes learning algorithms, equivalence oracles, and model checkers to identify any discrepancies between the expected and actual behaviors of the system.
 * </p>
 * @param <I> The type of input symbols at each step.
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 * @see VerificationResult
 */
@Slf4j
public class BlackBoxVerifier<I> {
    private static final Function<String, String> EDGE_PARSER = s -> s;
    /**
     * The membership oracle used to evaluate test cases and provide the system's output for given inputs.
     */
    @Getter
    MembershipOracle.MealyMembershipOracle<String, String> memOracle;
    /**
     * The System Under Learning (SUL) representing the black-box system to be verified.
     */
    private final SUL<String, String> verifiedSystem;
    /**
     * The learned Mealy machine that models the behavior of the black-box system based on test cases.
     */
    private MealyMachine<?, String, ?, String> learnedMealy;
    /**
     * The alphabet of input symbols used in the verification process.
     */
    private final Alphabet<String> inputAlphabet;
    /**
     * The learning algorithm used to learn the behavior of the black-box system from test cases.
     */
    private final LearningAlgorithm.MealyLearner<String, String> learner;
    /**
     * The equivalence oracle used to find counterexamples by comparing the learned model with the black-box system.
     */
    private final MealyEQOracleChain<String, String> eqOracle;
    /**
     * The adaptive STL updater that manages and updates the Signal Temporal Logic (STL) properties to be verified.
     */
    @Getter
    private final AdaptiveSTLUpdater<I> properties;
    /**
     * The model checker used to verify the learned Mealy machine against Signal Temporal Logic (STL) properties.
     */
    private final ModelChecker.MealyModelChecker<String, String, String, MealyMachine<?, String, ?, String>> modelChecker;
    /**
     * A list of timeout oracles used to manage timeouts for equivalence oracle operations.
     */
    private final List<TimeoutEQOracle<String, String>> timeoutOracles = new ArrayList<>();
    /**
     * The timeout value in seconds used for equivalence oracle operations.
     */
    private Long timeout = null;

    /**
     * @param memOracle     The membership oracle
     * @param properties    The LTL properties to be verified. What we verify is the conjunction of the properties.
     * @param inputAlphabet The input alphabet.
     */
    public BlackBoxVerifier(MembershipOracle.MealyMembershipOracle<String, String> memOracle, SUL<String, String> verifiedSystem, AdaptiveSTLUpdater<I> properties, Alphabet<String> inputAlphabet) {
        this.properties = properties;
        this.properties.setInputAlphabet(inputAlphabet);
        this.inputAlphabet = inputAlphabet;
        this.memOracle = memOracle;
        this.verifiedSystem = verifiedSystem;
        // Since the omega membership query is difficult for Simulink model, we allow only finite property

        // create a learner
        this.learner = new TTTLearnerMealy<>(this.inputAlphabet, memOracle, AcexAnalyzers.LINEAR_FWD);


        // Create model checker
        modelChecker = new LTSminMonitorIOBuilder<String, String>()
                .withString2Input(EDGE_PARSER).withString2Output(EDGE_PARSER).create();

        // create an equivalence oracle, that first searches for a counter example using the ltl properties, and next
        this.eqOracle = new MealyEQOracleChain<>(this.properties);
    }

    public void addWpMethodEQOracle(int maxDepth) {
        addEqOracle(new MealyWpMethodEQOracle<>(memOracle, maxDepth));
    }

    public void addBFOracle(double multiplier) {
        addEqOracle(new MealyBFInclusionOracle<>(memOracle, multiplier));
    }

    public void addRandomWordEQOracle(int minLength, int maxLength, int maxTests, Random random, int batchSize) {
        addEqOracle(new MealyRandomWordsEQOracle<>(
                memOracle, minLength, maxLength, maxTests, random, batchSize));
    }

    public void addRandomWalkEQOracle(double restartProbability, long maxSteps, Random random) {
        addEqOracle(new RandomWalkEQOracle<>(verifiedSystem, restartProbability, maxSteps, random));

    }

    public void addCompleteExplorationEQOracle(int minDepth, int maxDepth, int batchSize) {
        addEqOracle(new MealyCompleteExplorationEQOracle<>(
                memOracle, minDepth, maxDepth, batchSize));
    }

    /**
     * Add a corner case equivalence oracle.
     * <p>This oracle tries the corner case input, i.e., the inputs with the same values</p>
     *
     * @param length  The length of the input.
     * @param minStep The minimum step of the corner case.
     */
    public EvaluationCountable.MealyEquivalenceOracle<String, String> addCornerCaseEQOracle(int length, int minStep) {
        MealyFixedSetEQOracle cornerCaseEqOracle =
                new MealyFixedSetEQOracle(this.getProperties().list(), this.memOracle);
        int step = length;
        while (step >= minStep) {
            List<Word<String>> cornerCase = new ArrayList<>();
            int finalStep = step;
            while (cornerCase.isEmpty() || cornerCase.get(0).size() < length) {
                List<Word<String>> newSuffixes = inputAlphabet.stream().map(c ->
                        Word.fromList(Collections.nCopies(finalStep, c))).collect(Collectors.toList());
                if (cornerCase.isEmpty()) {
                    cornerCase = newSuffixes;
                } else {
                    cornerCase = cornerCase.stream().flatMap(prefix ->
                            newSuffixes.stream().map(prefix::concat)).collect(Collectors.toList());
                }
            }
            // Limit the length of each corner cases and add them to the oracle
            cornerCase.stream().map(word -> word.prefix(length)).forEach(cornerCaseEqOracle::add);
            step /= 2;
        }
        addEqOracle(cornerCaseEqOracle);

        return cornerCaseEqOracle;
    }

    public void addEqOracle(PropertyOracle.MealyEquivalenceOracle<String, String> eqOracle) {
        if (Objects.nonNull(timeout)) {
            TimeoutEQOracle<String, String> timeoutOracle = new TimeoutEQOracle<>(
                    new StopDisprovedEQOracle<>(eqOracle, this.properties), timeout);
            this.eqOracle.addOracle(timeoutOracle);
            timeoutOracles.add(timeoutOracle);
        } else {
            this.eqOracle.addOracle(new StopDisprovedEQOracle<>(eqOracle, this.properties));
        }
    }

    /**
     * Set timeout to the equivalence oracle added next time.
     *
     * @param timeout timeout in seconds.
     */
    public void setTimeout(long timeout) {
        this.timeout = timeout;
    }

    /**
     * Run black-box checking.
     * <p>
     * The equivalence oracles are tried in the order of their addition until a counterexample is found, all the
     * target specifications are falsified, or all the equivalence oracles are exhausted. Then, the counterexamples are
     * extracted from the final learned Mealy machine and validated by the SUL. A failure of the SUL execution is
     * reported as {@link TerminationReason#EXECUTION_FAILURE} instead of an exception. If the failure happens while
     * validating the counterexamples, the counterexamples validated before the failure are still reported.
     *
     * @return the result of black-box checking
     */
    public VerificationResult<I> run() {
        for (TimeoutEQOracle<String, String> timeoutOracle : timeoutOracles) {
            timeoutOracle.start();
        }
        RoundCountingExperiment experiment = new RoundCountingExperiment(learner, eqOracle, this.inputAlphabet);
        try {
            this.learnedMealy = experiment.run();
            return processMealy(experiment.rounds());
        } catch (SULException e) {
            log.error("Black-box checking is aborted because the execution of the SUL failed", e);
            properties.reset();
            int states = Objects.isNull(learnedMealy) ? 0 : learnedMealy.size();
            return new VerificationResult<>(List.of(), properties.getSTLProperties(), properties.size(),
                    TerminationReason.EXECUTION_FAILURE, new Statistics(experiment.rounds(), states), Optional.of(e));
        }
    }

    /**
     * Wirte the DOT of the Mealy machine witnessing a counterexample.
     *
     * @param cex The counterexample
     * @param a   Write the DOT to {@code a}
     * @throws IOException The exception by GraphDOT.write
     */
    public void writeDOTCex(Counterexample<?> cex, Appendable a) throws IOException {
        GraphDOT.write(cex.witness(), this.inputAlphabet, a);
    }

    /**
     * Wirte the DOT of the learned Mealy machine.
     *
     * @param a Write the DOT to {@code a}
     * @throws IOException The exception by GraphDOT.write
     */
    public void writeDOTLearnedMealy(Appendable a) throws IOException {
        GraphDOT.write(learnedMealy, this.inputAlphabet, a);
    }

    /**
     * Visualize the Mealy machine witnessing a counterexample.
     */
    public void visualizeCex(Counterexample<?> cex) {
        Visualization.visualize(cex.witness(), this.inputAlphabet);
    }

    /**
     * Visualize the learned Mealy machine
     */
    public void visualizeLearnedMealy() {
        Visualization.visualize(this.learnedMealy, this.inputAlphabet);
    }

    /**
     * Write the ETF of the learned Mealy machine.
     *
     * @param os Write the ETF to {@code os}
     */
    public void writeETFLearnedMealy(OutputStream os) {
        Mealy2ETFWriterIO<String, String> writer = Mealy2ETFWriterIO.getInstance();
        writer.writeModel(os, learnedMealy, this.inputAlphabet);
    }

    /**
     * Extract the counterexamples from the learned Mealy machine and validate them by the SUL.
     *
     * @param rounds the number of the learning rounds
     * @return the result of black-box checking
     */
    private VerificationResult<I> processMealy(int rounds) {
        // The reason of the termination must be decided before resetting the properties
        TerminationReason reason;
        if (properties.allDisproved()) {
            reason = TerminationReason.ALL_TARGETS_FALSIFIED;
        } else if (timeoutOracles.stream().anyMatch(TimeoutEQOracle::hasTimedOut)) {
            reason = TerminationReason.TIMEOUT;
        } else {
            reason = TerminationReason.EQUIVALENCE_TESTING_EXHAUSTED;
        }
        // Reset the list of properties to the initial one
        properties.reset();

        List<Counterexample<I>> counterexamples = new ArrayList<>();
        List<TemporalLogic<I>> unresolved = new ArrayList<>();
        Optional<Throwable> failure = Optional.empty();
        for (TemporalLogic<I> stlProperty : properties.getSTLProperties()) {
            String ltlProperty = properties.toLTLString(stlProperty);

            final MealyMachine<?, String, ?, String> witness =
                    modelChecker.findCounterExample(learnedMealy, this.inputAlphabet, ltlProperty);
            if (Objects.isNull(witness)) {
                unresolved.add(stlProperty);
                continue;
            }
            // We found the counter example Mealy machine.
            List<Word<String>> cexInputs = stateCover(witness, this.inputAlphabet);
            Word<String> input = cexInputs.get(cexInputs.size() - 1);
            final Word<String> sutOutput;
            try {
                sutOutput = memOracle.answerQuery(input);
            } catch (SULException e) {
                // Keep the counterexamples validated so far and report the failure
                log.error("The execution of the SUL failed while validating the counterexample {} for {}", input, stlProperty, e);
                unresolved.add(stlProperty);
                if (failure.isEmpty()) {
                    failure = Optional.of(e);
                    reason = TerminationReason.EXECUTION_FAILURE;
                }
                continue;
            }
            boolean confirmed = violates(ltlProperty, input, sutOutput);
            Counterexample<I> cex = new Counterexample<>(stlProperty, input, witness.computeOutput(input),
                    sutOutput, confirmed, witness);
            counterexamples.add(cex);
            if (!confirmed) {
                log.warn("The counterexample {} for {} is not confirmed by the SUL: the learned model outputs {} but the SUL outputs {}",
                        input, stlProperty, cex.hypothesisOutput(), cex.sutOutput());
                unresolved.add(stlProperty);
            }
        }

        return new VerificationResult<>(counterexamples, unresolved, properties.size(), reason,
                new Statistics(rounds, learnedMealy.size()), failure);
    }

    /**
     * Checks if an observed trace violates an LTL formula.
     * <p>
     * We check the formula by the same model checker as the learned Mealy machine. The Mealy machine given to the model
     * checker has only the observed trace, so the semantics is the same as the check of the learned Mealy machine
     * restricted to this trace.
     *
     * @param ltlProperty the LTL formula
     * @param input       the input word of the trace
     * @param output      the output word of the trace
     * @return {@code true} if and only if the trace violates {@code ltlProperty}
     */
    private boolean violates(String ltlProperty, Word<String> input, Word<String> output) {
        CompactMealy<String, String> trace = new CompactMealy<>(this.inputAlphabet);
        int state = trace.addInitialState();
        for (int i = 0; i < input.size(); i++) {
            int next = trace.addState();
            trace.addTransition(state, input.getSymbol(i), next, output.getSymbol(i));
            state = next;
        }
        return Objects.nonNull(modelChecker.findCounterExample(trace, this.inputAlphabet, ltlProperty));
    }

    /**
     * A {@link MealyExperiment} exposing the number of the learning rounds.
     */
    private static final class RoundCountingExperiment extends MealyExperiment<String, String> {
        RoundCountingExperiment(LearningAlgorithm.MealyLearner<String, String> learner,
                                EquivalenceOracle.MealyEquivalenceOracle<String, String> eqOracle,
                                Alphabet<String> inputs) {
            super(learner, eqOracle, inputs);
        }

        int rounds() {
            return getRound();
        }
    }
}
