package org.group_mmm;

import de.learnlib.api.oracle.PropertyOracle;
import org.slf4j.LoggerFactory;
import org.uma.jmetal.algorithm.singleobjective.geneticalgorithm.SteadyStateGeneticAlgorithm;
import org.uma.jmetal.operator.CrossoverOperator;
import org.uma.jmetal.operator.MutationOperator;
import org.uma.jmetal.operator.SelectionOperator;
import org.uma.jmetal.solution.IntegerSolution;
import org.uma.jmetal.util.evaluator.SolutionListEvaluator;

import java.util.List;
import java.util.Objects;

/**
 * <p>SimulinkSteadyStateGeneticAlgorithm class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class SimulinkSteadyStateGeneticAlgorithm extends SteadyStateGeneticAlgorithm<IntegerSolution> {
    private static final org.slf4j.Logger LOGGER = LoggerFactory.getLogger(SimulinkSteadyStateGeneticAlgorithm.class);
    private EQSearchProblem problem;
    private PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle;

    SimulinkSteadyStateGeneticAlgorithm(EQSearchProblem problem, int maxEvaluations, int populationSize, CrossoverOperator<IntegerSolution> crossoverOperator, MutationOperator<IntegerSolution> mutationOperator, SelectionOperator<List<IntegerSolution>, IntegerSolution> selectionOperator, SolutionListEvaluator<IntegerSolution> evaluator, PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle) {
        super(problem, maxEvaluations, populationSize, crossoverOperator, mutationOperator, selectionOperator);
        this.problem = problem;
        this.ltlOracle = ltlOracle;
    }

    /** {@inheritDoc} */
    @Override
    protected boolean isStoppingConditionReached() {
        if (super.isStoppingConditionReached()) {
            LOGGER.debug("Stop because it reached maxEvaluations");
            return true;
        }
        return ltlOracle.isDisproved() || problem.isStopped();
    }

    /**
     * {@inheritDoc}
     *
     * Create initial population only for the initial run
     */
    @Override
    protected List<IntegerSolution> createInitialPopulation() {
        if (Objects.isNull(this.population)) {
            LOGGER.debug("new population is generated");
            return super.createInitialPopulation();
        } else {
            LOGGER.debug("previous population is reused");
            return this.population;
        }
    }
}
