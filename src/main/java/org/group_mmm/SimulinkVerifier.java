package org.group_mmm;

import de.learnlib.acex.analyzers.AcexAnalyzers;
import de.learnlib.algorithms.ttt.mealy.TTTLearnerMealy;
import de.learnlib.api.SUL;
import de.learnlib.api.algorithm.LearningAlgorithm;
import de.learnlib.api.logging.LoggingPropertyOracle;
import de.learnlib.api.oracle.*;
import de.learnlib.filter.cache.sul.SULCache;
import de.learnlib.mapper.MappedSUL;
import de.learnlib.oracle.emptiness.MealyBFEmptinessOracle;
import de.learnlib.oracle.equivalence.CExFirstOracle;
import de.learnlib.oracle.equivalence.EQOracleChain;
import de.learnlib.oracle.equivalence.MealyBFInclusionOracle;
import de.learnlib.oracle.equivalence.WpMethodEQOracle;
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
import java.util.function.Function;

import static net.automatalib.util.automata.Automata.stateCover;

/**
 * SimulinkVerifier is the interface of the verifier of a Simulink model.
 *
 * @author Masaki Waga <mwaga@nii.ac.jp>
 */
class SimulinkVerifier {
    private static final Function<String, String> EDGE_PARSER = s -> s;

    final private double multiplier = 1.0;
    private MealyMachine<?, String, ?, String> learnedMealy;
    private MealyMachine<?, String, ?, String> cexMealy;
    private Alphabet<String> abstractInputAlphabet;
    private Alphabet<ArrayList<Double>> concreteInputAlphabet;
    protected SUL<ArrayList<Double>, ArrayList<Double>> simulink;
    private SimulinkSULMapper mapper;
    private LearningAlgorithm.MealyLearner<String, String> learner;
    private EquivalenceOracle.MealyEquivalenceOracle<String, String> eqOracle;
    private List<String> properties;
    private Word<String> cexInput;
    private String cexProperty;
    private Word<String> cexOutput;
    private ModelChecker.MealyModelChecker<String, String, String, MealyMachine<?, String, ?, String>> modelChecker;



    /**
     * @param initScript The MATLAB script called at first. You have to define mdl in the script.
     * @param paramName  The list of input parameters.
     * @param signalStep The signal step in the simulatin
     * @param properties The LTL properties to be verified
     * @param mapper     The I/O mapepr between abstract/concrete Simulink models.
     * @throws Exception It can be thrown from the constrcutor of SimulinkSUL.
     */
    SimulinkVerifier(String initScript, ArrayList<String> paramName, double signalStep, List<String> properties, SimulinkSULMapper mapper) throws Exception {
        this.properties = properties;
        this.mapper = mapper;
        this.simulink = new SimulinkSUL(initScript, paramName, signalStep);
        this.concreteInputAlphabet = mapper.constructConcreteAlphabet();
        this.abstractInputAlphabet = mapper.constructAbstractAlphabet();

        this.simulink = SULCache.createTreeCache(this.concreteInputAlphabet, this.simulink);

        MappedSUL<String, String, ArrayList<Double>, ArrayList<Double>> mappedSimulink = new MappedSUL<>(mapper, simulink);

        // Since the omega membership query is difficult for Simulink model, we allow only finite property

        // create a regular membership oracle
        MembershipOracle.MealyMembershipOracle<String, String> memOracle = SULCache.createTreeCache(abstractInputAlphabet, mappedSimulink);

        // create a learner
        this.learner = new TTTLearnerMealy<>(this.abstractInputAlphabet, memOracle, AcexAnalyzers.LINEAR_FWD);


        // Create model checker
        modelChecker = new LTSminMonitorIOBuilder<String, String>()
                .withString2Input(EDGE_PARSER).withString2Output(EDGE_PARSER).create();

        // create an emptiness oracle, that is used to disprove properties
        EmptinessOracle.MealyEmptinessOracle<String, String>
                emptinessOracle = new MealyBFEmptinessOracle<>(memOracle, multiplier);

        // create an inclusion oracle, that is used to find counterexamples to hypotheses
        InclusionOracle.MealyInclusionOracle<String, String>
                inclusionOracle = new MealyBFInclusionOracle<>(memOracle, multiplier);

        assert properties.size() == 1;
        // create an LTL property oracle, that also logs stuff
        PropertyOracle.MealyPropertyOracle<String, String, String> ltl =
                new LoggingPropertyOracle.MealyLoggingPropertyOracle<>(
                        new MealyFinitePropertyOracle<>(properties.get(0), inclusionOracle, emptinessOracle, modelChecker));

        // create an equivalence oracle, that first searches for a counter example using the ltl properties, and next
        // with the W-method.
        this.eqOracle = new EQOracleChain.MealyEQOracleChain<>(
                new CExFirstOracle.MealyCExFirstOracle<>(ltl),
                new WpMethodEQOracle.MealyWpMethodEQOracle<>(memOracle, 3));
    }

    public String getCexProperty() {
        return cexProperty;
    }

    public Word<String> getCexInput() {
        return cexInput;
    }

    public Word<String> getCexOutput() {
        return cexOutput;
    }

    /**
     * @return Returns {@code true} if and only if the Simulink model is verified i.e., no counter example is found.
     */
    boolean run() {
        // create an experiment
        Experiment.MealyExperiment<String, String>
                experiment = new Experiment.MealyExperiment<>(learner, eqOracle, abstractInputAlphabet);
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
    void writeDOT(Appendable a) throws IOException {
        GraphDOT.write(cexMealy, abstractInputAlphabet, a);
    }

    /**
     * Visualize the found counter example.
     */
    void visualize() {
        Visualization.visualize(cexMealy, abstractInputAlphabet);
    }

    /**
     * Set the counter example input/output.
     *
     * @return Returns {@code true} if and only if the Simulink model is verified i.e., no counter example is found.
     */
    private boolean processMealy() {
        for (String property : properties) {
            final MealyMachine<?, String, ?, String> cexMealyCandidate =
                    modelChecker.findCounterExample(learnedMealy, abstractInputAlphabet, property);
            if (Objects.isNull(cexMealyCandidate)) {
                continue;
            }
            // We found the counter example Mealy machine.
            cexMealy = cexMealyCandidate;
            cexProperty = property;
            List<Word<String>> cexInputs = stateCover(cexMealy, abstractInputAlphabet);
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
