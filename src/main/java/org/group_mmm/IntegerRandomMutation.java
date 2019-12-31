package org.group_mmm;

import org.jetbrains.annotations.NotNull;
import org.uma.jmetal.operator.MutationOperator;
import org.uma.jmetal.solution.IntegerSolution;

import java.util.Objects;
import java.util.Random;

/**
 * This class implements a random mutation operator for integer solution.
 *
 * @author Masaki Waga
 */
public class IntegerRandomMutation implements MutationOperator<IntegerSolution> {
    private double mutationProbability;
    private Random random;

    /**
     * <p>Constructor for IntegerRandomMutation.</p>
     *
     * @param mutationProbability a double.
     * @param random a {@link java.util.Random} object.
     */
    public IntegerRandomMutation(double mutationProbability, Random random) {
        this.mutationProbability = mutationProbability;
        this.random = random;
    }

    IntegerRandomMutation(double mutationProbability) {
        this.mutationProbability = mutationProbability;
        this.random = new Random();
    }

    /** {@inheritDoc} */
    @NotNull
    @Override
    public IntegerSolution execute(IntegerSolution solution) {
        assert (Objects.nonNull(solution));

        for (int i = 0; i < solution.getNumberOfVariables(); i++) {
            if (Math.random() < mutationProbability) {
                Integer value = random.nextInt(solution.getUpperBound(i) + 1) + solution.getLowerBound(i);
                solution.setVariableValue(i, value);
            }
        }
        return solution;
    }
}
