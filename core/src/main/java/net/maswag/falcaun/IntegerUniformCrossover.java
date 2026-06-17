package net.maswag.falcaun;

import org.uma.jmetal.operator.CrossoverOperator;
import org.uma.jmetal.solution.IntegerSolution;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Random;

/**
 * Uniform crossover for integers
 *
 * @author Masaki Waga
 */
public class IntegerUniformCrossover implements CrossoverOperator<IntegerSolution> {
    private double crossoverProbability;
    private final Random random;

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
        this.random = new Random(0);
    }

    /**
     * <p>Constructor for IntegerUniformCrossover.</p>
     *
     * @param crossoverProbability a double.
     */
    public IntegerUniformCrossover(double crossoverProbability) {
        this(crossoverProbability, new Random(0));
    }

    /**
     * <p>Constructor for IntegerUniformCrossover.</p>
     *
     * @param crossoverProbability a double.
     * @param random               a {@link java.util.Random} object.
     */
    public IntegerUniformCrossover(double crossoverProbability, Random random) {
        this.crossoverProbability = crossoverProbability;
        this.random = random;
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
            if (random.nextDouble() < crossoverProbability) {
                int tmp = offspring.get(0).getVariableValue(i);
                offspring.get(0).setVariableValue(i, offspring.get(1).getVariableValue(i));
                offspring.get(1).setVariableValue(i, tmp);
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
