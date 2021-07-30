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

    public double getCrossoverProbability() {
        return crossoverProbability;
    }

    public void setCrossoverProbability(double crossoverProbability) {
        this.crossoverProbability = crossoverProbability;
    }

    /**
     * <p>Constructor for IntegerUniformCrossover.</p>
     */
    public IntegerUniformCrossover() {
        this.crossoverProbability = 0.5;
    }

    /**
     * <p>Constructor for IntegerUniformCrossover.</p>
     *
     * @param crossoverProbability a double.
     */
    public IntegerUniformCrossover(double crossoverProbability) {
        this.crossoverProbability = crossoverProbability;
    }

    /** {@inheritDoc} */
    @Override
    public List<IntegerSolution> execute(List<IntegerSolution> integerSolutions) {
        assert (Objects.nonNull(integerSolutions));
        assert (integerSolutions.size() == 2);

        List<IntegerSolution> offspring = new ArrayList<>(2);
        offspring.add((IntegerSolution) integerSolutions.get(0).copy());
        offspring.add((IntegerSolution) integerSolutions.get(1).copy());
        for (int i = 0; i < integerSolutions.get(0).getNumberOfVariables(); i++) {
            if (Math.random() < crossoverProbability) {
                int tmp = offspring.get(0).getVariables().get(i);
                offspring.get(0).getVariables().set(i, offspring.get(1).getVariables().get(i));
                offspring.get(1).getVariables().set(i, tmp);
            }
        }
        return offspring;
    }

    /**
     * <p>getNumberOfRequiredParents.</p>
     *
     * @return a int.
     */
    @Override
    public int getNumberOfRequiredParents() {
        return 2;
    }

    /**
     * <p>getNumberOfGeneratedChildren.</p>
     *
     * @return a int.
     */
    @Override
    public int getNumberOfGeneratedChildren() {
        return 2;
    }
}
