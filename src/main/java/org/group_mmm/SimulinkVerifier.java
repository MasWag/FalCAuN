package org.group_mmm;

import de.learnlib.api.SUL;
import de.learnlib.api.oracle.PropertyOracle;
import de.learnlib.filter.cache.sul.SULCache;
import de.learnlib.mapper.MappedSUL;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;

import java.io.IOException;
import java.io.OutputStream;
import java.util.*;
import java.util.function.Function;

/**
 * Verifier of a Simulink model
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class SimulinkVerifier {
    protected SUL<List<Double>, List<Double>> simulink;
    private SimulinkSUL rawSimulink;
    private Alphabet<String> abstractInputAlphabet;
    private Alphabet<List<Double>> concreteInputAlphabet;
    private SimulinkSULMapper mapper;
    private SUL<String, String> mappedSimulink;
    private BlackBoxVerifier verifier;
    private SimulinkMembershipOracle memOracle;
    private List<SimulinkMembershipOracleCost> memOracleCosts = new ArrayList<>();

    /**
     * <p>Constructor for SimulinkVerifier.</p>
     *
     * @param initScript The MATLAB script called at first. You have to define mdl in the script.
     * @param paramName  The list of input parameters.
     * @param signalStep The signal step in the simulatin
     * @param properties The LTL properties to be verified
     * @param mapper     The I/O mapepr between abstract/concrete Simulink models.
     * @throws java.lang.Exception It can be thrown from the constructor of SimulinkSUL.
     */
    public SimulinkVerifier(String initScript, List<String> paramName, double signalStep, List<String> properties, SimulinkSULMapper mapper) throws Exception {
        this.mapper = mapper;
        this.rawSimulink = new SimulinkSUL(initScript, paramName, signalStep);
        this.concreteInputAlphabet = mapper.constructConcreteAlphabet();
        this.abstractInputAlphabet = mapper.constructAbstractAlphabet();

        this.simulink = SULCache.createTreeCache(this.concreteInputAlphabet, rawSimulink);

        this.mappedSimulink = new MappedSUL<>(mapper, simulink);
        this.mappedSimulink = SULCache.createTreeCache(this.abstractInputAlphabet, this.mappedSimulink);
        // create a regular membership oracle
        this.memOracle = new SimulinkMembershipOracle(rawSimulink, this.mapper);
        verifier = new BlackBoxVerifier(this.memOracle, mappedSimulink, properties, abstractInputAlphabet);
    }

    List<String> getCexProperty() {
        return verifier.getCexProperty();
    }

    void addSimulinkEqOracle(Function<Word<List<Double>>, Double> costFunc,
                             Function<SimulinkMembershipOracleCost,
                                     PropertyOracle.MealyEquivalenceOracle<String, String>> constructor) {
        // Define the cost function from a discrete input signal to a double using the Simulink model and the STL formula
        SimulinkMembershipOracleCost oracle =
                new SimulinkMembershipOracleCost(this.rawSimulink, this.mapper, costFunc);
        oracle.setCache(this.memOracle.getCache());
        memOracleCosts.add(oracle);

        this.verifier.addEqOracle(constructor.apply(oracle));
    }

    void addWpMethodEQOracle(int maxDepth) {
        this.verifier.addWpMethodEQOracle(maxDepth);
    }

    void addBFOracle(double multiplier) {
        this.verifier.addBFOracle(multiplier);
    }

    void addRandomWordEQOracle(int minLength, int maxLength, int maxTests, Random random, int batchSize) {
        this.verifier.addRandomWordEQOracle(minLength, maxLength, maxTests, random, batchSize);
    }

    void addRandomWalkEQOracle(double restartProbability, long maxSteps, Random random) {
        this.verifier.addRandomWalkEQOracle(restartProbability, maxSteps, random);
    }

    void addCompleteExplorationEQOracle(int minDepth, int maxDepth, int batchSize) {
        this.verifier.addCompleteExplorationEQOracle(minDepth, maxDepth, batchSize);
    }

    /**
     * Set timeout to the equivalence oracle added next time.
     *
     * @param timeout timeout in seconds.
     */
    void setTimeout(long timeout) {
        this.verifier.setTimeout(timeout);
    }

    void addHillClimbingEQOracle(Function<Word<List<Double>>, Double> costFunc,
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
     * @param ltlOracle      a {@link de.learnlib.api.oracle.PropertyOracle.MealyPropertyOracle} object.
     */
    public void addHillClimbingEQOracle(Function<Word<List<Double>>, Double> costFunc,
                                        int length,
                                        Random random,
                                        int maxTests,
                                        int generationSize,
                                        int childrenSize,
                                        boolean resetWord,
                                        PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle) {
        this.addSimulinkEqOracle(costFunc, oracle ->
                new HillClimbingEQOracle(oracle, length, random, maxTests, generationSize, childrenSize, resetWord, ltlOracle));
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
     * @param ltlOracle      a {@link de.learnlib.api.oracle.PropertyOracle.MealyPropertyOracle} object.
     */
    public void addSAEQOracle(Function<Word<List<Double>>, Double> costFunc,
                              int length,
                              Random random,
                              int maxTests,
                              int generationSize,
                              int childrenSize,
                              boolean resetWord,
                              double alpha,
                              PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle) {
        this.addSimulinkEqOracle(costFunc, oracle ->
                new SAEQOracle(oracle, length, random, maxTests, generationSize, childrenSize, resetWord, alpha, ltlOracle));
    }

    /**
     * <p>getLtlFormulas.</p>
     *
     * @return a {@link java.util.ArrayList} object.
     */
    public ArrayList<PropertyOracle.MealyPropertyOracle<String, String, String>> getLtlFormulas() {
        return verifier.getLtlFormulas();
    }

    void addMutateSelectEQOracle(Function<Word<List<Double>>, Double> costFunc,
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
    void addGAEQOracle(Function<Word<List<Double>>, Double> costFunc,
                       int length,
                       int maxTests,
                       ArgParser.GASelectionKind selectionKind,
                       int generationSize,
                       double crossoverProb,
                       double mutationProbability, // e.g., 1.0 / length
                       PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle) {
        this.addSimulinkEqOracle(costFunc, oracle ->
                new GAEQOracle(oracle, length, maxTests, selectionKind, generationSize, crossoverProb, mutationProbability, ltlOracle));
    }

    List<Word<String>> getCexAbstractInput() {
        return verifier.getCexInput();
    }

    List<Word<List<Double>>> getCexConcreteInput() {
        return this.mapper.mapInputs(getCexAbstractInput());
    }


    List<Word<String>> getCexOutput() {
        return verifier.getCexOutput();
    }

    /**
     * <p>run.</p>
     *
     * @return Returns {@code true} if and only if the Simulink model is verified i.e., no counter example is found.
     */
    public boolean run() {
        Set<SimulinkMembershipOracleCost> tmp = new HashSet<>(memOracleCosts);
        for (SimulinkMembershipOracleCost memOracleCost : memOracleCosts) {
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
    void writeDOTCex(int index, Appendable a) throws IOException {
        verifier.writeDOTCex(index, a);
    }

    /**
     * Wirte the DOT of the learned Mealy machine
     *
     * @param a Write the DOT to {@code a}
     * @throws IOException The exception by GraphDOT.write
     */
    void writeDOTLearnedMealy(Appendable a) throws IOException {
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
    void visualizeCex(int index) {
        this.verifier.visualizeCex(index);
    }

    /**
     * Visualize the learned Mealy machine
     */
    void visualizeLearnedMealy() {
        this.verifier.visualizeLearnedMealy();
    }

    /**
     * Modify the simulation step of Simulink.
     *
     * @param simulinkSimulationStep The fixed simulation step of Simulink. If this value is too large, Simulink can abort due to an computation error.
     */
    public void setSimulationStep(double simulinkSimulationStep) {
        this.rawSimulink.setSimulationStep(simulinkSimulationStep);
    }

    /**
     * @return the number of the Simulink executions
     */
    public int getSimulinkCount() {
        return this.rawSimulink.getCounter();
    }
}
