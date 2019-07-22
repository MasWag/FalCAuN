package org.group_mmm;

import de.learnlib.api.oracle.EquivalenceOracle;
import de.learnlib.api.oracle.PropertyOracle;
import de.learnlib.api.query.DefaultQuery;
import net.automatalib.automata.transducers.MealyMachine;
import net.automatalib.words.Word;
import org.uma.jmetal.algorithm.Algorithm;
import org.uma.jmetal.operator.CrossoverOperator;
import org.uma.jmetal.operator.MutationOperator;
import org.uma.jmetal.operator.impl.crossover.IntegerSBXCrossover;
import org.uma.jmetal.operator.impl.mutation.IntegerPolynomialMutation;
import org.uma.jmetal.operator.impl.selection.BestSolutionSelection;
import org.uma.jmetal.solution.IntegerSolution;
import org.uma.jmetal.util.AlgorithmRunner;
import org.uma.jmetal.util.comparator.ObjectiveComparator;
import org.uma.jmetal.util.evaluator.impl.SequentialSolutionListEvaluator;

import javax.annotation.Nullable;
import javax.annotation.ParametersAreNonnullByDefault;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;

class GAEQOracle implements EquivalenceOracle.MealyEquivalenceOracle<String, String> {
    private Algorithm<IntegerSolution> algorithm;
    private EQSearchProblem problem;

    GAEQOracle(SimulinkMembershipOracleCost memOracle, int length, int maxEvaluations, int populationSize, double crossoverProb, double distributionIndex, PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle) {
        this.problem = new EQSearchProblem(memOracle, length);
        CrossoverOperator<IntegerSolution> crossoverOperator = new IntegerSBXCrossover(crossoverProb, distributionIndex);
        MutationOperator<IntegerSolution> mutationOperator = new IntegerPolynomialMutation();
        Comparator<IntegerSolution> fitnessComparator = new ObjectiveComparator<>(0);

        this.algorithm = new SimulinkGenerationalGeneticAlgorithm(
                problem,
                maxEvaluations,
                populationSize,
                crossoverOperator,
                mutationOperator,
                new BestSolutionSelection<>(fitnessComparator.reversed()),
                new SequentialSolutionListEvaluator<>(),
                ltlOracle);
    }

    @Nullable
    @Override
    @ParametersAreNonnullByDefault
    public DefaultQuery<String, Word<String>> findCounterExample(MealyMachine<?, String, ?, String> hypothesis, Collection<? extends String> symbolList) {
        problem.setHypothesis(hypothesis);
        problem.setSymbolList(new ArrayList<>(symbolList));
        new AlgorithmRunner.Executor(algorithm);
        if (problem.isStopped()) {
            return problem.getCexQuery();
        }
        return null;
    }
}