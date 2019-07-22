package org.group_mmm;

import de.learnlib.api.oracle.PropertyOracle;
import org.uma.jmetal.algorithm.singleobjective.geneticalgorithm.GenerationalGeneticAlgorithm;
import org.uma.jmetal.operator.CrossoverOperator;
import org.uma.jmetal.operator.MutationOperator;
import org.uma.jmetal.operator.SelectionOperator;
import org.uma.jmetal.solution.IntegerSolution;
import org.uma.jmetal.util.evaluator.SolutionListEvaluator;

import java.util.List;

public class SimulinkGenerationalGeneticAlgorithm extends GenerationalGeneticAlgorithm<IntegerSolution> {
    private EQSearchProblem problem;
    private PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle;

    SimulinkGenerationalGeneticAlgorithm(EQSearchProblem problem, int maxEvaluations, int populationSize, CrossoverOperator<IntegerSolution> crossoverOperator, MutationOperator<IntegerSolution> mutationOperator, SelectionOperator<List<IntegerSolution>, IntegerSolution> selectionOperator, SolutionListEvaluator<IntegerSolution> evaluator, PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle) {
        super(problem, maxEvaluations, populationSize, crossoverOperator, mutationOperator, selectionOperator, evaluator);
        this.problem = problem;
        this.ltlOracle = ltlOracle;
    }

    @Override
    protected boolean isStoppingConditionReached() {
        return super.isStoppingConditionReached() || ltlOracle.isDisproved() || problem.isStopped();
    }
}
