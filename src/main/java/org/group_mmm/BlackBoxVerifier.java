package org.group_mmm;

import de.learnlib.acex.analyzers.AcexAnalyzers;
import de.learnlib.algorithms.ttt.mealy.TTTLearnerMealy;
import de.learnlib.api.SUL;
import de.learnlib.api.algorithm.LearningAlgorithm;
import de.learnlib.api.logging.LoggingPropertyOracle;
import de.learnlib.api.oracle.EmptinessOracle;
import de.learnlib.api.oracle.InclusionOracle;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.oracle.PropertyOracle;
import de.learnlib.oracle.emptiness.MealyBFEmptinessOracle;
import de.learnlib.oracle.equivalence.*;
import de.learnlib.oracle.equivalence.mealy.RandomWalkEQOracle;
import de.learnlib.oracle.property.MealyFinitePropertyOracle;
import de.learnlib.util.Experiment;
import net.automatalib.automata.transducers.MealyMachine;
import net.automatalib.modelcheckers.ltsmin.monitor.LTSminMonitorIOBuilder;
import net.automatalib.modelchecking.ModelChecker;
import net.automatalib.serialization.dot.GraphDOT;
import net.automatalib.visualization.Visualization;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Random;
import java.util.function.Function;

import static net.automatalib.util.automata.Automata.stateCover;

/**
 * Verifier of a black-box system
 *
 * @author Masaki Waga <masaki@gmail.com>
 */
class BlackBoxVerifier {
    private static final Function<String, String> EDGE_PARSER = s -> s;
    final private double multiplier = 1.0;
    private SUL<String, String> verifiedSystem;
    MembershipOracle.MealyMembershipOracle<String, String> memOracle;
    private MealyMachine<?, String, ?, String> learnedMealy;
    private MealyMachine<?, String, ?, String> cexMealy;
    private Alphabet<String> inputAlphabet;
    private LearningAlgorithm.MealyLearner<String, String> learner;
    private EQOracleChain.MealyEQOracleChain<String, String> eqOracle;
    private List<String> properties;
    private Word<String> cexInput;
    private String cexProperty;
    private Word<String> cexOutput;
    private ModelChecker.MealyModelChecker<String, String, String, MealyMachine<?, String, ?, String>> modelChecker;


    /**
     * @param memOracle     The membership oracle
     * @param properties    The LTL properties to be verified. What we verify is the conjunction of the properties.
     * @param inputAlphabet The input alphabet.
     */
    BlackBoxVerifier(MembershipOracle.MealyMembershipOracle<String, String> memOracle, SUL<String, String> verifiedSystem, List<String> properties, Alphabet<String> inputAlphabet) {
        this.properties = properties;
        this.inputAlphabet = inputAlphabet;
        this.memOracle = memOracle;
        this.verifiedSystem = verifiedSystem;
        // Since the omega membership query is difficult for Simulink model, we allow only finite property

        // create a learner
        this.learner = new TTTLearnerMealy<>(this.inputAlphabet, memOracle, AcexAnalyzers.LINEAR_FWD);


        // Create model checker
        modelChecker = new LTSminMonitorIOBuilder<String, String>()
                .withString2Input(EDGE_PARSER).withString2Output(EDGE_PARSER).create();

        // create an emptiness oracle, that is used to disprove properties
        EmptinessOracle.MealyEmptinessOracle<String, String>
                emptinessOracle = new MealyBFEmptinessOracle<>(memOracle, multiplier);

        // create an inclusion oracle, that is used to find counterexamples to hypotheses
        InclusionOracle.MealyInclusionOracle<String, String>
                inclusionOracle = new MealyBFInclusionOracle<>(memOracle, multiplier);

        // create an LTL property oracle, that also logs stuff
        ArrayList<PropertyOracle.MealyPropertyOracle<String, String, String>> ltlFormulas = new ArrayList<>();
        for (String property : properties) {
            PropertyOracle.MealyPropertyOracle<String, String, String> ltl =
                    new LoggingPropertyOracle.MealyLoggingPropertyOracle<>(
                            new MealyFinitePropertyOracle<>(property, inclusionOracle, emptinessOracle, modelChecker));
            ltlFormulas.add(ltl);
        }

        // create an equivalence oracle, that first searches for a counter example using the ltl properties, and next
        this.eqOracle = new EQOracleChain.MealyEQOracleChain<>(
                new CExFirstOracle.MealyCExFirstOracle<>(ltlFormulas));
    }

    public MembershipOracle.MealyMembershipOracle<String, String> getMemOracle() {
        return memOracle;
    }

    void addEqOracle(PropertyOracle.MealyEquivalenceOracle<String, String> eqOracle) {
        this.eqOracle.addOracle(eqOracle);
    }

    void addWpMethodEQOracle(int maxDepth) {
        addEqOracle(new WpMethodEQOracle.MealyWpMethodEQOracle<>(memOracle, maxDepth));
    }

    void addBFOracle(double multiplier) {
        addEqOracle(new MealyBFInclusionOracle<>(memOracle, multiplier));
    }

    void addRandomWordEQOracle(int minLength, int maxLength, int maxTests, Random random, int batchSize) {
        addEqOracle(new RandomWordsEQOracle.MealyRandomWordsEQOracle<>(
                memOracle, minLength, maxLength, maxTests, random, batchSize));
    }

    void addRandomWalkEQOracle(double restartProbability, long maxSteps, Random random) {
        addEqOracle(new RandomWalkEQOracle<>(verifiedSystem, restartProbability, maxSteps, random));
    }

    void addCompleteExplorationEQOracle(int minDepth, int maxDepth, int batchSize) {
        addEqOracle(new CompleteExplorationEQOracle.MealyCompleteExplorationEQOracle<>(
                memOracle, minDepth, maxDepth, batchSize));
    }

    String getCexProperty() {
        return cexProperty;
    }

    Word<String> getCexInput() {
        return cexInput;
    }

    Word<String> getCexOutput() {
        return cexOutput;
    }

    /**
     * @return Returns {@code true} if and only if the given black-box system is verified i.e., no counter example is found.
     */
    boolean run() {
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
    void writeDOTCex(Appendable a) throws IOException {
        GraphDOT.write(cexMealy, this.inputAlphabet, a);
    }

    /**
     * Wirte the DOT of the learned Mealy machine.
     *
     * @param a Write the DOT to {@code a}
     * @throws IOException The exception by GraphDOT.write
     */
    void writeDOTLearnedMealy(Appendable a) throws IOException {
        GraphDOT.write(learnedMealy, this.inputAlphabet, a);
    }

    /**
     * Visualize the found counter example.
     */
    void visualizeCex() {
        Visualization.visualize(cexMealy, this.inputAlphabet);
    }

    /**
     * Visualize the learned Mealy machine
     */
    void visualizeLearnedMealy() {
        Visualization.visualize(this.learnedMealy, this.inputAlphabet);
    }

    /**
     * Set the counter example input/output.
     *
     * @return Returns {@code true} if and only if the black-box system is verified i.e., no counter example is found.
     */
    private boolean processMealy() {
        for (String property : properties) {
            final MealyMachine<?, String, ?, String> cexMealyCandidate =
                    modelChecker.findCounterExample(learnedMealy, this.inputAlphabet, property);
            if (Objects.isNull(cexMealyCandidate)) {
                continue;
            }
            // We found the counter example Mealy machine.
            cexMealy = cexMealyCandidate;
            cexProperty = property;
            List<Word<String>> cexInputs = stateCover(cexMealy, this.inputAlphabet);
            cexInput = cexInputs.get(cexInputs.size() - 1);
            cexOutput = cexMealy.computeOutput(cexInput);

            return false;
        }
        cexMealy = null;
        cexProperty = null;
        cexInput = null;
        cexOutput = null;
        return true;
    }
}
