package org.group_mmm;

import java.util.function.Function;

public class Main {

    /**
     * A function that transforms edges in an FSM source to actual input for a DFA.
     */
    public static final Function<String, Character> EDGE_PARSER = s -> s.charAt(0);

    public static void main(String[] args) {
        System.out.println("Hello World!!");
/*
        //! @todo Parameterize
        String initScript = "initAFC";
        //! @todo Parameterize
        ArrayList<String> paramName = new ArrayList<>(Arrays.asList("aa", "ab"));
        //! @todo Parameterize
        double signalStep = 10;
        //! @todo Parameterize
        ArrayList<Map<Character, Double>> rawMapper = new ArrayList<>();
        SimulinkInputMapper inputMapper = new SimulinkInputMapper(rawMapper);
        Alphabet<SimulinkInput> sigma = inputMapper.constructAlphabet();

        SimulinkSUL simulink;

        try {
            simulink = new SimulinkSUL(initScript, paramName, signalStep);
        } catch (Exception e) {
            System.out.println(e);
            return;
        }
        SULMapper<String, String, SimulinkInput, SimulinkOutput>
                mapper = new StringMapper<>(sigma);

        // Since the omega membership query is difficult for Simulink model, we allow only finite property

        // create an omega membership oracle
        // MealyOmegaMembershipOracle<?, Character, Character> omqOracle = new MealySimulatorOmegaOracle<>(mealy);

        // create a regular membership oracle
        MembershipOracle.MealyMembershipOracle<Character, Character> mqOracle; //= omqOracle.getMembershipOracle();

        // create a learner
        LearningAlgorithm.MealyLearner<Character, Character> learner = new TTTLearnerMealy<>(sigma, mqOracle, AcexAnalyzers.LINEAR_FWD);

        // create a model checker
        ModelCheckerLasso.MealyModelCheckerLasso<Character, Character, String> modelChecker =
                new LTSminLTLAlternatingBuilder<Character, Character>().withString2Input(EDGE_PARSER).
                        withString2Output(EDGE_PARSER).create();

        //! @todo I should make this a parameter.
        double multiplier = 10.0;
        // create an emptiness oracle, that is used to disprove properties
        EmptinessOracle.MealyEmptinessOracle<Character, Character>
                emptinessOracle = new MealyBFEmptinessOracle<>(mqOracle, multiplier);

        // create an inclusion oracle, that is used to find counterexamples to hypotheses
        InclusionOracle.MealyInclusionOracle<Character, Character> inclusionOracle = new MealyBFInclusionOracle<>(mqOracle, 1.0);

        // create an LTL property oracle, that also logs stuff
        PropertyOracle.MealyPropertyOracle<Character, Character, String> ltl = new LoggingPropertyOracle.MealyLoggingPropertyOracle<>(
                new MealyFinitePropertyOracle<>("X X X letter==\"2\"", inclusionOracle, emptinessOracle, modelChecker));


        // create an equivalence oracle, that first searches for a counter example using the ltl properties, and next
        // with the W-method.
        @SuppressWarnings("unchecked")
        EquivalenceOracle.MealyEquivalenceOracle<Character, Character> eqOracle = new EQOracleChain.MealyEQOracleChain<>(
                new CExFirstOracle.MealyCExFirstOracle<>(ltl),
                new WpMethodEQOracle.MealyWpMethodEQOracle<>(mqOracle, 3));

        // create an experiment
        Experiment.MealyExperiment<Character, Character>
                experiment = new Experiment.MealyExperiment<>(learner, eqOracle, sigma);

        // run the experiment
        experiment.run();

        // get the final result
        MealyMachine<?, Character, ?, Character> result = experiment.getFinalHypothesis();

        // check we have the correct result
        assert DeterministicEquivalenceTest.findSeparatingWord(mealy, result, sigma) == null;
        */
    }
}
