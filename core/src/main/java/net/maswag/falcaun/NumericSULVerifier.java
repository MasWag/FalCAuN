package net.maswag.falcaun;

import lombok.extern.slf4j.Slf4j;
import de.learnlib.sul.SUL;
import de.learnlib.oracle.PropertyOracle.MealyPropertyOracle;
import de.learnlib.mapper.MappedSUL;
import net.automatalib.alphabet.Alphabet;
import net.maswag.falcaun.parser.TemporalLogic;

import java.io.IOException;
import java.io.OutputStream;
import java.util.*;
import java.util.function.Function;

import static de.learnlib.filter.cache.sul.SULCaches.createTreeCache;

/**
 * Verifies a Numeric System Under Learning (NumericSUL) against specified properties using various equivalence oracles and model checking techniques.
 * <p>This class provides a framework for verifying the behavior of a numeric system under learning by comparing it against a set of Signal Temporal Logic (STL) properties.
 * It uses learning algorithms, equivalence oracles, and model checkers to identify any discrepancies between the expected and actual behaviors.</p>
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class NumericSULVerifier implements AutoCloseable {
    protected final NumericSUL sul;
    private final SignalDiscretizer signalDiscretizer;
    private final BlackBoxVerifier<List<Double>> verifier;
    private final NumericMembershipOracle memOracle;
    private final EvaluationCountable.Sum evaluationCountables = new EvaluationCountable.Sum();
    private final double signalStep;

    /**
     * <p>Constructor for NumericSULVerifier.</p>
     *
     * @param sul        The system under test.
     * @param signalStep The signal step in the simulation
     * @param properties The LTL properties to be verified
     * @param signalDiscretizer     The I/O mapper between the abstract and concrete signals.
     */
    public NumericSULVerifier(NumericSUL sul, double signalStep, AdaptiveSTLUpdater<List<Double>> properties, SignalDiscretizer signalDiscretizer) {
        log.debug("Initialize numeric SUL verifier with signalStep: {}, properties: {}", signalStep, properties);
        this.sul = sul;
        this.signalStep = signalStep;
        this.signalDiscretizer = signalDiscretizer;
        Alphabet<List<Double>> concreteInputAlphabet = signalDiscretizer.constructConcreteAlphabet();
        Alphabet<String> abstractInputAlphabet = signalDiscretizer.constructAbstractAlphabet();

        // The step-wise SUL with the LearnLib caches. It is used only by the equivalence oracles executing the SUL step by step.
        SUL<List<Double>, IOSignalPiece<List<Double>>> cachedSUL = createTreeCache(concreteInputAlphabet, sul);
        SUL<String, String> mappedSUL = createTreeCache(abstractInputAlphabet, new MappedSUL<>(signalDiscretizer, cachedSUL));
        // create a regular membership oracle
        this.memOracle = new NumericMembershipOracle(sul, this.signalDiscretizer);
        properties.setMemOracle(memOracle);
        verifier = new BlackBoxVerifier<>(this.memOracle, mappedSUL, properties, abstractInputAlphabet);
    }

    /**
     * Add an equivalence oracle guided by the robustness of the given cost function.
     * The SUL executions and their caches are shared with the membership oracle.
     */
    void addRobustnessEqOracle(Function<IOSignal<List<Double>>, Double> costFunc,
                               Function<RobustnessOracle,
                                       ? extends EvaluationCountable.MealyEquivalenceOracle<String, String>> constructor) {
        RobustnessOracle oracle = this.memOracle.registerCostFunction(costFunc);
        EvaluationCountable.MealyEquivalenceOracle<String, String> eqOracle = constructor.apply(oracle);
        evaluationCountables.add(eqOracle);
        this.verifier.addEqOracle(eqOracle);
    }

    public void addWpMethodEQOracle(int maxDepth) {
        this.verifier.addWpMethodEQOracle(maxDepth);
    }

    public void addBFOracle(double multiplier) {
        this.verifier.addBFOracle(multiplier);
    }

    public void addRandomWordEQOracle(int minLength, int maxLength, int maxTests, Random random, int batchSize) {
        this.verifier.addRandomWordEQOracle(minLength, maxLength, maxTests, random, batchSize);
    }

    public void addRandomWalkEQOracle(double restartProbability, long maxSteps, Random random) {
        this.verifier.addRandomWalkEQOracle(restartProbability, maxSteps, random);
    }

    public void addCompleteExplorationEQOracle(int minDepth, int maxDepth, int batchSize) {
        this.verifier.addCompleteExplorationEQOracle(minDepth, maxDepth, batchSize);
    }

    /**
     * Add a corner case equivalence oracle.
     * <p>This oracle tries the corner case input, i.e., the inputs with the same values</p>
     * @param length The length of the input.
     * @param minStep The minimum step of the corner case.
     */
    public void addCornerCaseEQOracle(int length, int minStep) {
        this.evaluationCountables.add(this.verifier.addCornerCaseEQOracle(length, minStep));
    }

    /**
     * Set timeout to the equivalence oracle added next time.
     *
     * @param timeout timeout in seconds.
     */
    public void setTimeout(long timeout) {
        this.verifier.setTimeout(timeout);
    }

    public void addHillClimbingEQOracle(TemporalLogic.STLCost costFunc,
                                        int length,
                                        Random random,
                                        int maxTests,
                                        int generationSize,
                                        int childrenSize,
                                        boolean resetWord) {
        this.addRobustnessEqOracle(costFunc, oracle ->
                new HillClimbingEQOracle(oracle, length, random, maxTests, generationSize, childrenSize, resetWord));
    }

    /**
     * <p>addHillClimbingEQOracle.</p>
     *
     * @param costFunc       a {@link java.util.function.Function} object.
     * @param length         a int.
     * @param random         a {@link java.util.Random} object.
     * @param maxTests       a int.
     * @param generationSize a int.
     * @param childrenSize   a int.
     * @param resetWord      a boolean.
     * @param ltlOracle      a {@link de.learnlib.oracle.PropertyOracle.MealyPropertyOracle} object.
     */
    public void addHillClimbingEQOracle(Function<IOSignal<List<Double>>, Double> costFunc,
                                        int length,
                                        Random random,
                                        int maxTests,
                                        int generationSize,
                                        int childrenSize,
                                        boolean resetWord,
                                        MealyPropertyOracle<String, String, String> ltlOracle) {
        this.addRobustnessEqOracle(costFunc, oracle ->
                new HillClimbingEQOracle(oracle, length, random, maxTests, generationSize, childrenSize, resetWord, ltlOracle));
    }

    public void addHillClimbingEQOracleAll(int length,
                                           Random random,
                                           int maxTests,
                                           int generationSize,
                                           int childrenSize,
                                           boolean resetWord) {
        for (int i = 0; i < this.getProperties().size(); i++) {
            this.addHillClimbingEQOracle(this.getProperties().getSTLProperties().get(i),
                    length, random, maxTests, generationSize, childrenSize, resetWord, this.getProperties().list().get(i));

        }
    }

    /**
     * <p>addSAEQOracle.</p>
     *
     * @param costFunc       a {@link java.util.function.Function} object.
     * @param length         a int.
     * @param random         a {@link java.util.Random} object.
     * @param maxTests       a int.
     * @param generationSize a int.
     * @param childrenSize   a int.
     * @param resetWord      a boolean.
     * @param alpha          a double.
     * @param ltlOracle      a {@link de.learnlib.oracle.PropertyOracle.MealyPropertyOracle} object.
     */
    public void addSAEQOracle(Function<IOSignal<List<Double>>, Double> costFunc,
                              int length,
                              Random random,
                              int maxTests,
                              int generationSize,
                              int childrenSize,
                              boolean resetWord,
                              double alpha,
                              MealyPropertyOracle<String, String, String> ltlOracle) {
        this.addRobustnessEqOracle(costFunc, oracle ->
                new SAEQOracle(oracle, length, random, maxTests, generationSize, childrenSize, resetWord, alpha, ltlOracle));
    }

    void addMutateSelectEQOracle(Function<IOSignal<List<Double>>, Double> costFunc,
                                 int length,
                                 Random random,
                                 int maxTests,
                                 int generationSize,
                                 int childrenSize,
                                 int changeSize,
                                 boolean resetWord) {
        this.addRobustnessEqOracle(costFunc, oracle ->
                new MutateSelectEQOracle(oracle, length, random, maxTests, generationSize, childrenSize, resetWord, changeSize));
    }

    /**
     * add a Genetic algorithm-based equivalence oracle
     *
     * @param costFunc            The cost function assigning a Double to each OutputSignal. This is typically an STL formula.
     * @param length              length of the generated signals
     * @param maxTests            maximum test size
     * @param selectionKind       kind of the selection method
     * @param generationSize      size of each generation. This must be an even number.
     * @param crossoverProb       probability to have crossover
     * @param mutationProbability probability to have mutation
     * @param ltlOracle           the LTL formula
     */
    public void addGAEQOracle(Function<IOSignal<List<Double>>, Double> costFunc,
                       int length,
                       int maxTests,
                       GASelectionKind selectionKind,
                       int generationSize,
                       double crossoverProb,
                       double mutationProbability, // e.g., 1.0 / length
                       MealyPropertyOracle<String, String, String> ltlOracle) {
        this.addRobustnessEqOracle(costFunc, oracle ->
                new GAEQOracle(oracle, length, maxTests, selectionKind, generationSize, crossoverProb, mutationProbability, ltlOracle));
    }

    /**
     * Returns the concrete input signal of a counterexample.
     *
     * @param cex a counterexample in the result of {@link #run()}
     * @return the concrete input signal constructed from the abstract input of {@code cex}
     */
    public Signal concreteInput(VerificationResult.Counterexample<?> cex) {
        Signal result = new Signal(this.signalStep);
        result.addAll(this.signalDiscretizer.mapInput(cex.abstractInput()));
        return result;
    }

    /**
     * Run black-box checking.
     *
     * @return the result of black-box checking including the statistics of the SUL executions
     * @see BlackBoxVerifier#run()
     */
    public VerificationResult<List<Double>> run() {
        VerificationResult<List<Double>> result = verifier.run();
        return result.withStatistics(new VerificationResult.Statistics(
                result.statistics().learningRounds(),
                result.statistics().hypothesisStates(),
                OptionalInt.of(getSutExecutionCount()),
                OptionalInt.of(getEqEvaluationCount()),
                OptionalDouble.of(getSimulationTimeSecond())));
    }

    /**
     * Wirte the DOT of the Mealy machine witnessing a counterexample.
     *
     * @param cex a counterexample in the result of {@link #run()}
     * @param a   Write the DOT to {@code a}
     * @throws IOException The exception by GraphDOT.write
     */
    public void writeDOTCex(VerificationResult.Counterexample<?> cex, Appendable a) throws IOException {
        verifier.writeDOTCex(cex, a);
    }

    /**
     * Wirte the DOT of the learned Mealy machine
     *
     * @param a Write the DOT to {@code a}
     * @throws IOException The exception by GraphDOT.write
     */
    public void writeDOTLearnedMealy(Appendable a) throws IOException {
        verifier.writeDOTLearnedMealy(a);
    }

    /**
     * Write the ETF of the learned Mealy machine.
     *
     * @param os Write the ETF to {@code os}
     */
    public void writeETFLearnedMealy(OutputStream os) {
        verifier.writeETFLearnedMealy(os);
    }

    /**
     * Visualize the Mealy machine witnessing a counterexample.
     *
     * @param cex a counterexample in the result of {@link #run()}
     */
    public void visualizeCex(VerificationResult.Counterexample<?> cex) {
        this.verifier.visualizeCex(cex);
    }

    /**
     * Visualize the learned Mealy machine
     */
    public void visualizeLearnedMealy() {
        this.verifier.visualizeLearnedMealy();
    }

    /**
     * @return the number of the executions of the SUL
     */
    public int getSutExecutionCount() {
        return this.sul.getExecutionCount();
    }

    /**
     * Returns the number of the evaluations of input words by the equivalence oracles.
     * <p>
     * This is not necessarily the number of the SUL executions by the equivalence oracles. For example, the
     * corner-case equivalence oracle counts every evaluated word, including the ones answered by a cache, while the
     * robustness-based equivalence oracles count only the actual executions.
     *
     * @return the number of the evaluations of input words by the equivalence oracles
     */
    public int getEqEvaluationCount() {
        return evaluationCountables.getEvaluateCount();
    }

    /**
     * @return Signal Temporal Logic (STL) properties to be verified
     */
    public AdaptiveSTLUpdater<List<Double>> getProperties() {
        return this.verifier.getProperties();
    }

    public void addSAEQOracleAll(int length, Random random, int maxTest, int generationSize, int childrenSize, boolean resetWord, double alpha) {
        for (int i = 0; i < this.getProperties().size(); i++) {
            this.addSAEQOracle(this.getProperties().getSTLProperties().get(i),
                    length, random, maxTest, generationSize, childrenSize, resetWord, alpha, this.getProperties().list().get(i));
        }
    }

    public void addGAEQOracleAll(int length, int maxTest, GASelectionKind selectionKind, int populationSize, double crossoverProb, double mutationProb) {
        for (int i = 0; i < this.getProperties().size(); i++) {
            this.addGAEQOracle(this.getProperties().getSTLProperties().get(i),
                    length, maxTest, selectionKind, populationSize, crossoverProb, mutationProb, this.getProperties().list().get(i));
        }
    }

    /**
     * Close the SUL, e.g., the MATLAB engine or the Python interpreter.
     */
    @Override
    public void close() throws Exception {
        this.sul.close();
    }

    /**
     * @return the execution time for the simulations
     */
    public double getSimulationTimeSecond() {
        return this.sul.getSimulationTimeSecond();
    }
}
