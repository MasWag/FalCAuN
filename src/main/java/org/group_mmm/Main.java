package org.group_mmm;

import de.learnlib.acex.analyzers.AcexAnalyzers;
import de.learnlib.algorithms.ttt.mealy.TTTLearnerMealy;
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
import net.automatalib.modelcheckers.ltsmin.monitor.LTSminMonitorAlternating;
import net.automatalib.words.Alphabet;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Map;
import java.util.function.Function;

public class Main {

    /**
     * A function that transforms edges in an FSM source to actual input for a DFA.
     */
//    public static final Function<String, String> EDGE_PARSER = s -> s.charAt(0);

    public static void main(String[] args) {
        System.out.println("Hello World!!");

        //! @todo Parameterize
        String initScript = "initAFC";
        //! @todo Parameterize
        ArrayList<String> paramName = new ArrayList<>(Arrays.asList("aa", "ab"));
        //! @todo Parameterize
        double signalStep = 10;
        //! @todo Parameterize
        ArrayList<Map<Character, Double>> inputMapper = new ArrayList<>();
        //! @todo Parameterize
        ArrayList<Character> largestOutputs = new ArrayList<>();
        //! @todo Parameterize
        ArrayList<Map<Character, Double>> outputMapper = new ArrayList<>();

        SimulinkSULMapper mapper = new SimulinkSULMapper(inputMapper, largestOutputs, outputMapper);
        Alphabet<ArrayList<Double>> concreteAlphabet = mapper.constructConcreteAlphabet();
        Alphabet<String> abstractAlphabet = mapper.constructAbstractAlphabet();

        SimulinkSUL simulink;

        try {
            simulink = new SimulinkSUL(initScript, paramName, signalStep);
        } catch (Exception e) {
            System.out.println(e.getMessage());
            return;
        }

        SULCache<ArrayList<Double>, ArrayList<Double>> cachedSimulink = SULCache.createTreeCache(concreteAlphabet, simulink);

        MappedSUL<String, String, ArrayList<Double>, ArrayList<Double>> mapperSimulink = new MappedSUL<>(mapper, cachedSimulink);

        // Since the omega membership query is difficult for Simulink model, we allow only finite property

        // create a regular membership oracle
        MembershipOracle.MealyMembershipOracle<String, String> mqOracle = SULCache.createTreeCache(abstractAlphabet, mapperSimulink);

        // create a learner
        LearningAlgorithm.MealyLearner<String, String> learner = new TTTLearnerMealy<>(abstractAlphabet, mqOracle, AcexAnalyzers.LINEAR_FWD);

        // create a model checker
        //ModelCheckerLasso.MealyModelCheckerLasso<String, String, String> modelChecker =
        //      new LTSminLTLAlternatingBuilder<String, String>().create();
        //! @todo Parameterize
        boolean keepFiles = true;
        LTSminMonitorAlternating<String, String>
                modelChecker = new LTSminMonitorAlternating<>(keepFiles, Function.identity(), Function.identity(), Collections.emptyList());

        //! @todo I should make this a parameter.
        double multiplier = 10.0;
        // create an emptiness oracle, that is used to disprove properties
        EmptinessOracle.MealyEmptinessOracle<String, String>
                emptinessOracle = new MealyBFEmptinessOracle<>(mqOracle, multiplier);

        // create an inclusion oracle, that is used to find counterexamples to hypotheses
        InclusionOracle.MealyInclusionOracle<String, String>
                inclusionOracle = new MealyBFInclusionOracle<>(mqOracle, 1.0);

        // create an LTL property oracle, that also logs stuff
        PropertyOracle.MealyPropertyOracle<String, String, String> ltl =
                new LoggingPropertyOracle.MealyLoggingPropertyOracle<>(
                new MealyFinitePropertyOracle<>("X X X letter==\"2\"", inclusionOracle, emptinessOracle, modelChecker));


        // create an equivalence oracle, that first searches for a counter example using the ltl properties, and next
        // with the W-method.
        EquivalenceOracle.MealyEquivalenceOracle<String, String> eqOracle = new EQOracleChain.MealyEQOracleChain<>(
                new CExFirstOracle.MealyCExFirstOracle<>(ltl),
                new WpMethodEQOracle.MealyWpMethodEQOracle<>(mqOracle, 3));

        // create an experiment
        Experiment.MealyExperiment<String, String>
                experiment = new Experiment.MealyExperiment<>(learner, eqOracle, abstractAlphabet);

        // run the experiment
        experiment.run();

        // get the final result
        MealyMachine<?, String, ?, String> result = experiment.getFinalHypothesis();
    }
}
