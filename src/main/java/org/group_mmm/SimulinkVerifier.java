package org.group_mmm;

import de.learnlib.api.SUL;
import de.learnlib.api.oracle.PropertyOracle;
import de.learnlib.filter.cache.sul.SULCache;
import de.learnlib.mapper.MappedSUL;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;

import java.io.IOException;
import java.util.*;
import java.util.function.Function;

/**
 * Verifier of a Simulink model
 *
 * @author Masaki Waga <masaki@gmail.com>
 */
class SimulinkVerifier {
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
     * @param initScript The MATLAB script called at first. You have to define mdl in the script.
     * @param paramName  The list of input parameters.
     * @param signalStep The signal step in the simulatin
     * @param properties The LTL properties to be verified
     * @param mapper     The I/O mapepr between abstract/concrete Simulink models.
     * @throws Exception It can be thrown from the constrcutor of SimulinkSUL.
     */
    SimulinkVerifier(String initScript, List<String> paramName, double signalStep, List<String> properties, SimulinkSULMapper mapper) throws Exception {
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

    void addEqOracle(PropertyOracle.MealyEquivalenceOracle<String, String> eqOracle) {
        this.verifier.addEqOracle(eqOracle);
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

    void addHillClimbingEQOracle(Function<Word<List<Double>>, Double> costFunc,
                                 int length,
                                 Random random,
                                 int maxTests,
                                 int generationSize,
                                 int childrenSize,
                                 boolean resetWord) {
        SimulinkMembershipOracleCost oracle =
                new SimulinkMembershipOracleCost(this.rawSimulink, this.mapper, costFunc);
        oracle.setCache(this.memOracle.getCache());
        memOracleCosts.add(oracle);

        this.verifier.addEqOracle(new HillClimbingEQOracle(oracle, length, random, maxTests, generationSize, childrenSize, resetWord));
    }

    void addHillClimbingEQOracle(Function<Word<List<Double>>, Double> costFunc,
                                 int length,
                                 Random random,
                                 int maxTests,
                                 int generationSize,
                                 int childrenSize,
                                 boolean resetWord,
                                 PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle) {
        SimulinkMembershipOracleCost oracle =
                new SimulinkMembershipOracleCost(this.rawSimulink, this.mapper, costFunc);
        oracle.setCache(this.memOracle.getCache());
        memOracleCosts.add(oracle);

        this.verifier.addEqOracle(new HillClimbingEQOracle(oracle, length, random, maxTests, generationSize, childrenSize, resetWord, ltlOracle));
    }


    ArrayList<PropertyOracle.MealyPropertyOracle<String, String, String>> getLtlFormulas() {
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
        SimulinkMembershipOracleCost oracle =
                new SimulinkMembershipOracleCost(this.rawSimulink, this.mapper, costFunc);
        oracle.setCache(this.memOracle.getCache());
        memOracleCosts.add(oracle);

        this.verifier.addEqOracle(new MutateSelectEQOracle(oracle, length, random, maxTests, generationSize, childrenSize, resetWord, changeSize));
    }

    void addGAEQOracle(Function<Word<List<Double>>, Double> costFunc,
                       int length,
                       Random random,
                       int maxTests,
                       int generationSize,
                       int childrenSize,
                       int changeSize,
                       double mutationProb,
                       double crossoverProb,
                       boolean resetWord
    ) {
        SimulinkMembershipOracleCost oracle =
                new SimulinkMembershipOracleCost(this.rawSimulink, this.mapper, costFunc);
        oracle.setCache(this.memOracle.getCache());
        memOracleCosts.add(oracle);

        this.verifier.addEqOracle(new GAEQOracle(oracle, length, random, maxTests, generationSize, childrenSize, changeSize, crossoverProb, mutationProb, resetWord));
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
     * @return Returns {@code true} if and only if the Simulink model is verified i.e., no counter example is found.
     */
    boolean run() {
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
}
