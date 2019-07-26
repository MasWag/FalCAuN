package org.group_mmm;

import org.uma.jmetal.operator.CrossoverOperator;
import org.uma.jmetal.solution.IntegerSolution;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * Uniform crossover for integers
 *
 * @author Masaki Waga
 */
public class IntegerUniformCrossover implements CrossoverOperator<IntegerSolution> {
    private double crossoverProbability;

    public IntegerUniformCrossover() {
        this.crossoverProbability = 0.5;
    }

    public IntegerUniformCrossover(double crossoverProbability) {
        this.crossoverProbability = crossoverProbability;
    }

    @Override
    public List<IntegerSolution> execute(List<IntegerSolution> integerSolutions) {
        assert (Objects.nonNull(integerSolutions));
        assert (integerSolutions.size() == 2);
        List<IntegerSolution> solutions = new ArrayList<>(integerSolutions);
        for (int i = 0; i < integerSolutions.get(0).getNumberOfVariables(); i++) {
            if (Math.random() < crossoverProbability) {
                int tmp = solutions.get(0).getVariableValue(i);
                solutions.get(0).setVariableValue(i, solutions.get(1).getVariableValue(i));
                solutions.get(1).setVariableValue(i, tmp);
            }
        }
        return integerSolutions;
    }

    public int getNumberOfRequiredParents() {
        return 2;
    }

    public int getNumberOfGeneratedChildren() {
        return 2;
    }
}
