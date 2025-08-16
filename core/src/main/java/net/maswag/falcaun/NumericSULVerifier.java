package net.maswag.falcaun;

import lombok.extern.slf4j.Slf4j;
import de.learnlib.sul.SUL;
import de.learnlib.oracle.PropertyOracle.MealyPropertyOracle;
import de.learnlib.mapper.MappedSUL;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.word.Word;

import java.io.IOException;
import java.io.OutputStream;
import java.util.*;
import java.util.function.Function;

import static de.learnlib.filter.cache.sul.SULCaches.createTreeCache;

/**
 * Verifies a Numeric System Under Learning (NumericSUL) against specified properties using various equivalence oracles and model checking techniques.
 *
 * This class provides a framework for verifying the behavior of a numeric system under learning by comparing it against a set of Signal Temporal Logic (STL) properties.
 * It uses learning algorithms, equivalence oracles, and model checkers to identify any discrepancies between the expected and actual behaviors.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class NumericSULVerifier {
    protected SUL<List<Double>, IOSignalPiece<List<Double>>> simulink;
    protected final NumericSUL rawSUL;
    private final NumericSULMapper mapper;
    private final BlackBoxVerifier<List<Double>> verifier;
    private final NumericMembershipOracle memOracle;
    private final List<NumericMembershipOracleCost> memOracleCosts = new ArrayList<>();
    private final EvaluationCountable.Sum evaluationCountables = new EvaluationCountable.Sum();
    private final double signalStep;

    /**
     * <p>Constructor for SimulinkVerifier.</p>
     *
     * @param rawSUL     The system under test.
     * @param signalStep The signal step in the simulation
     * @param properties The LTL properties to be verified
     * @param mapper     The I/O mapper between abstract/concrete Simulink models.
     */
    public NumericSULVerifier(NumericSUL rawSUL, double signalStep, AdaptiveSTLUpdater<List<Double>> properties, NumericSULMapper mapper) {
        log.debug("Initialize numeric SUL verifier with signalStep: {}, properties: {}", signalStep, properties);
        this.rawSUL = rawSUL;
        this.signalStep = signalStep;
        this.mapper = mapper;
        Alphabet<List<Double>> concreteInputAlphabet = mapper.constructConcreteAlphabet();
        Alphabet<String> abstractInputAlphabet = mapper.constructAbstractAlphabet();

        this.simulink = createTreeCache(concreteInputAlphabet, rawSUL);

        SUL<String, String> mappedSimulink = new MappedSUL<>(mapper, simulink);
        mappedSimulink = createTreeCache(abstractInputAlphabet, mappedSimulink);
        // create a regular membership oracle
        this.memOracle = new NumericMembershipOracle(rawSUL, this.mapper);
        properties.setMemOracle(memOracle);
        verifier = new BlackBoxVerifier<>(this.memOracle, mappedSimulink, properties, abstractInputAlphabet);
    }

    /**
     * Returns the falsified STL formulas in the string representation.
     */
    public List<TemporalLogic<List<Double>>> getCexProperty() {
        return verifier.getCexProperty();
    }

    void addSimulinkEqOracle(Function<IOSignal<List<Double>>, Double> costFunc,
                             Function<NumericMembershipOracleCost,
                                     ? extends EvaluationCountable.MealyEquivalenceOracle<String, String>> constructor) {
        // Define the cost function from a discrete input signal to a double using the Simulink model and the STL formula
        NumericMembershipOracleCost oracle =
                new NumericMembershipOracleCost(this.rawSUL, this.mapper, costFunc);
        oracle.setCache(this.memOracle.getCache());
        memOracleCosts.add(oracle);
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
        this.addSimulinkEqOracle(costFunc, oracle ->
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
        this.addSimulinkEqOracle(costFunc, oracle ->
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
        this.addSimulinkEqOracle(costFunc, oracle ->
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
        this.addSimulinkEqOracle(costFunc, oracle ->
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
        this.addSimulinkEqOracle(costFunc, oracle ->
                new GAEQOracle(oracle, length, maxTests, selectionKind, generationSize, crossoverProb, mutationProbability, ltlOracle));
    }

    public List<Word<String>> getCexAbstractInput() {
        return verifier.getCexInput();
    }

    public List<Signal> getCexConcreteInput() {
        List<Signal> result = new ArrayList<>();
        for (Word<String> abstractCex : this.getCexAbstractInput()) {
            result.add(new Signal(this.signalStep));
            result.get(result.size() - 1).addAll(this.mapper.mapInput(abstractCex));
        }
        return result;
    }


    public List<Word<String>> getCexOutput() {
        return verifier.getCexOutput();
    }

    /**
     * <p>run.</p>
     *
     * @return Returns {@code true} if and only if the Simulink model is verified i.e., no counter example is found.
     */
    public boolean run() {
        Set<NumericMembershipOracleCost> tmp = new HashSet<>(memOracleCosts);
        for (NumericMembershipOracleCost memOracleCost : memOracleCosts) {
            tmp.remove(memOracleCost);
            memOracleCost.addNotifiedAll(tmp);
        }

        return verifier.run();
    }

    /**
     * Wirte the DOT of the found counter example.
     *
     * @param a Write the DOT to {@code a}
     * @throws IOException The exception by GraphDOT.write
     */
    public void writeDOTCex(int index, Appendable a) throws IOException {
        verifier.writeDOTCex(index, a);
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
     * Visualize the found counter example.
     */
    public void visualizeCex(int index) {
        this.verifier.visualizeCex(index);
    }

    /**
     * Visualize the learned Mealy machine
     */
    public void visualizeLearnedMealy() {
        this.verifier.visualizeLearnedMealy();
    }

    /**
     * @return the number of the Simulink executions
     */
    public int getSimulinkCount() {
        return this.rawSUL.getCounter();
    }

    public int getSimulinkCountForEqTest() {
        return evaluationCountables.getEvaluateCount();
    }

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
     * Close the MATLAB engine. This method must be called when the object is no longer used.
     */
    public void close() throws Exception {
        this.rawSUL.close();
    }

    public double getSimulationTimeSecond() {
        return this.rawSUL.getSimulationTimeSecond();
    }
}
