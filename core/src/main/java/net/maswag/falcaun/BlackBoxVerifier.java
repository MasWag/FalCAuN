package net.maswag.falcaun;

import de.learnlib.acex.AcexAnalyzers;
import de.learnlib.algorithm.LearningAlgorithm;
import de.learnlib.algorithm.ttt.mealy.TTTLearnerMealy;
import de.learnlib.oracle.MembershipOracle;
import de.learnlib.oracle.PropertyOracle;
import de.learnlib.oracle.equivalence.*;
import de.learnlib.oracle.equivalence.mealy.RandomWalkEQOracle;
import de.learnlib.sul.SUL;
import de.learnlib.util.Experiment;
import lombok.Getter;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.modelchecker.ltsmin.monitor.LTSminMonitorIOBuilder;
import net.automatalib.modelchecking.ModelChecker;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.serialization.etf.writer.Mealy2ETFWriterIO;
import net.automatalib.visualization.Visualization;
import net.automatalib.word.Word;

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
 */
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
     * A list of Mealy machines representing counterexamples found during the verification process.
     */
    private List<MealyMachine<?, String, ?, String>> cexMealy;
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
     * A list of input words that led to counterexamples found during the verification process.
     */
    @Getter
    private List<Word<String>> cexInput;
    /**
     * A list of Signal Temporal Logic (STL) properties that were violated by the counterexamples found during the verification process.
     */
    @Getter
    private List<TemporalLogic<I>> cexProperty;
    /**
     * A list of output words produced by the black-box system for the counterexamples found during the verification process.
     */
    @Getter
    private List<Word<String>> cexOutput;
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
     * @return Returns {@code true} if and only if the given black-box system is verified i.e., no counter example is found.
     */
    public boolean run() {
        for (TimeoutEQOracle<String, String> timeoutOracle : timeoutOracles) {
            timeoutOracle.start();
        }
        // create an experiment
        Experiment.MealyExperiment<String, String>
                experiment = new Experiment.MealyExperiment<>(learner, eqOracle, this.inputAlphabet);
        this.learnedMealy = experiment.run();

        // run the experiment
        return processMealy();
    }

    /**
     * Wirte the DOT of the found counter example.
     *
     * @param a Write the DOT to {@code a}
     * @throws IOException The exception by GraphDOT.write
     */
    public void writeDOTCex(int index, Appendable a) throws IOException {
        GraphDOT.write(cexMealy.get(index), this.inputAlphabet, a);
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
     * Visualize the found counter example.
     */
    public void visualizeCex(int index) {
        Visualization.visualize(cexMealy.get(index), this.inputAlphabet);
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
     * Set the counter example input/output.
     *
     * @return Returns {@code true} if and only if the black-box system is verified i.e., no counter example is found for any system.
     */
    private boolean processMealy() {
        // Reset the list of properties to the initial one
        properties.reset();

        cexMealy = new ArrayList<>();
        cexProperty = new ArrayList<>();
        cexInput = new ArrayList<>();
        cexOutput = new ArrayList<>();
        boolean isVerified = true;
        for (TemporalLogic<I> stlProperty : properties.getSTLProperties()) {
            String ltlProperty = stlProperty.toLTLString();

            final MealyMachine<?, String, ?, String> cexMealyCandidate =
                    modelChecker.findCounterExample(learnedMealy, this.inputAlphabet, ltlProperty);
            if (!Objects.isNull(cexMealyCandidate)) {
                // We found the counter example Mealy machine.
                cexMealy.add(cexMealyCandidate);
                cexProperty.add(stlProperty);
                List<Word<String>> cexInputs = stateCover(cexMealyCandidate, this.inputAlphabet);
                Word<String> currentInput = cexInputs.get(cexInputs.size() - 1);
                cexInput.add(currentInput);
                cexOutput.add(cexMealyCandidate.computeOutput(currentInput));
                isVerified = false;
            }
        }

        return isVerified;
    }
}
