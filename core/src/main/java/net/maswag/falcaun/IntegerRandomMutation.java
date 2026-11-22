package net.maswag.falcaun;

import org.jetbrains.annotations.NotNull;
import org.uma.jmetal.operator.mutation.MutationOperator;
import org.uma.jmetal.solution.integersolution.IntegerSolution;

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

    public double getMutationProbability() {
        return mutationProbability;
    }

    public void setMutationProbability(double mutationProbability) {
        this.mutationProbability = mutationProbability;
    }

    /**
     * <p>Constructor for IntegerRandomMutation.</p>
     *
     * @param mutationProbability a double.
     * @param random              a {@link java.util.Random} object.
     */
    public IntegerRandomMutation(double mutationProbability, Random random) {
        this.mutationProbability = mutationProbability;
        this.random = random;
    }

    IntegerRandomMutation(double mutationProbability) {
        this.mutationProbability = mutationProbability;
        this.random = new Random(0);
    }

    /** {@inheritDoc} */
    @NotNull
    @Override
    public IntegerSolution execute(IntegerSolution solution) {
        assert (Objects.nonNull(solution));

        for (int i = 0; i < solution.variables().size(); i++) {
            if (this.random.nextDouble() < mutationProbability) {
                int positionToChange = this.random.nextInt(solution.variables().size());
                int lowerBound = solution.getBounds(positionToChange).getLowerBound();
                int upperBound = solution.getBounds(positionToChange).getUpperBound();
                Integer newValue = random.nextInt(upperBound - lowerBound + 1) + lowerBound;
                solution.variables().set(positionToChange, newValue);
            }
        }
        return solution;
    }

    /** {@inheritDoc} */
    @Override
    public double mutationProbability() {
        return mutationProbability;
    }
}
