package net.maswag.falcaun;

import de.learnlib.oracle.EquivalenceOracle;
import de.learnlib.oracle.PropertyOracle;
import de.learnlib.query.DefaultQuery;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.word.Word;
import org.slf4j.LoggerFactory;
import org.uma.jmetal.algorithm.Algorithm;
import org.uma.jmetal.operator.CrossoverOperator;
import org.uma.jmetal.operator.MutationOperator;
import org.uma.jmetal.operator.SelectionOperator;
import org.uma.jmetal.operator.impl.selection.BestSolutionSelection;
import org.uma.jmetal.operator.impl.selection.BinaryTournamentSelection;
import org.uma.jmetal.solution.IntegerSolution;
import org.uma.jmetal.util.AlgorithmRunner;
import org.uma.jmetal.util.comparator.ObjectiveComparator;
import org.uma.jmetal.util.evaluator.impl.SequentialSolutionListEvaluator;

import org.jetbrains.annotations.Nullable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;

/**
 * Equivalence query using genetic algorithm
 *
 * @author Masaki Waga
 *
 * <p>We use uniform crossover and random mutation.</p>
 */
class GAEQOracle implements EquivalenceOracle.MealyEquivalenceOracle<String, String>,
        EvaluationCountable.MealyEquivalenceOracle<String, String> {
    private final Algorithm<IntegerSolution> algorithm;
    private final EQSearchProblem problem;
    private static final org.slf4j.Logger LOGGER = LoggerFactory.getLogger(GAEQOracle.class);
    private final PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle;

    GAEQOracle(NumericMembershipOracleCost memOracle, int length, int maxEvaluations, ArgParser.GASelectionKind selectionKind, int populationSize, double crossoverProb, double mutationProbability, PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle) {

        this.problem = new EQSearchProblem(memOracle, length);
        CrossoverOperator<IntegerSolution> crossoverOperator = new IntegerUniformCrossover(crossoverProb);
        MutationOperator<IntegerSolution> mutationOperator = new IntegerRandomMutation(mutationProbability);
        Comparator<IntegerSolution> fitnessComparator = new ObjectiveComparator<>(0);
        this.ltlOracle = ltlOracle;

        SelectionOperator<List<IntegerSolution>, IntegerSolution> selection;

        switch (selectionKind) {
            case BestSolution:
                selection = new BestSolutionSelection<>(fitnessComparator);
                break;
            case Tournament:
                selection = new BinaryTournamentSelection<>(fitnessComparator);
                break;
            default:
                selection = null;
                break;
        }

        // We use steady state GA because, otherwise, it converged to a suboptimal point. Perhaps we can improve by parameter tuning.
        // See also https://www.researchgate.net/post/Whats_the_difference_between_the_steady_state_genetic_algorithm_and_the_generational_genetic_algorithm
        this.algorithm = new EQSteadyStateGeneticAlgorithm(
                problem,
                maxEvaluations,
                populationSize,
                crossoverOperator,
                mutationOperator,
                selection,
                new SequentialSolutionListEvaluator<>(),
                ltlOracle);
    }

    /**
     * @return whether the property is disproved.
     */
    private boolean isDisproved() {
        return ltlOracle.isDisproved();
    }

    /** {@inheritDoc} */
    @Nullable
    @Override
    public DefaultQuery<String, Word<String>> findCounterExample(MealyMachine<?, String, ?, String> hypothesis, Collection<? extends String> symbolList) {
        if (isDisproved()) {
            LOGGER.info("The specification is already disproved!!");
            return null;
        }
        // Fail fast on empty inputs
        if (symbolList.isEmpty()) {
            LOGGER.warn("Passed empty set of inputs to equivalence oracle; no counterexample can be found!");
            return null;
        }
        problem.setHypothesis(hypothesis);
        problem.setSymbolList(new ArrayList<>(symbolList));
        new AlgorithmRunner.Executor(algorithm).execute();
        if (problem.isStopped()) {
            LOGGER.info("Counter example is found!! {}", problem.getCexQuery());
            return problem.getCexQuery();
        }
        LOGGER.info("Counter example is NOT found :(");
        return null;
    }

    public int getEvaluateCount() {
        return problem.getEvaluateCount();
    }
}
