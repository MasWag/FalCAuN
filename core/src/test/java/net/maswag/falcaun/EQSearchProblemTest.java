package net.maswag.falcaun;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.uma.jmetal.solution.integersolution.IntegerSolution;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests of the search space and the operators of the GA-based equivalence oracle.
 * See BouncingBallGAEQOracleTest in the examples module for the falsification with the GA-based equivalence oracle.
 */
class EQSearchProblemTest {
    private static final int LENGTH = 5;
    private final List<String> symbolList = Arrays.asList("a", "b", "c");
    private EQSearchProblem problem;

    @BeforeEach
    void setUp() {
        // The membership oracle is not used because no solution is evaluated
        problem = new EQSearchProblem(null, LENGTH);
        problem.setSymbolList(symbolList);
    }

    @Test
    void boundsFollowSymbolList() {
        problem.setSymbolList(symbolList.subList(0, 2));
        IntegerSolution solution = problem.createSolution();
        assertEquals(LENGTH, solution.variables().size());
        assertEquals(0, solution.getBounds(0).getLowerBound());
        assertEquals(1, solution.getBounds(0).getUpperBound());

        // A solution in a reused population must see the bounds for the new symbol list
        problem.setSymbolList(symbolList);
        assertEquals(2, solution.getBounds(LENGTH - 1).getUpperBound());
    }

    @Test
    void mutationRespectsBounds() {
        IntegerRandomMutation mutation = new IntegerRandomMutation(1.0, new Random(0));
        assertEquals(1.0, mutation.mutationProbability());
        for (int i = 0; i < 100; i++) {
            IntegerSolution solution = mutation.execute(problem.createSolution());
            for (int value : solution.variables()) {
                assertTrue(0 <= value && value < symbolList.size());
            }
        }
    }

    @Test
    void crossoverSwapsVariables() {
        IntegerSolution parent0 = problem.createSolution();
        IntegerSolution parent1 = problem.createSolution();
        Collections.fill(parent0.variables(), 0);
        Collections.fill(parent1.variables(), 2);
        IntegerUniformCrossover crossover = new IntegerUniformCrossover(1.0, new Random(0));
        assertEquals(2, crossover.numberOfRequiredParents());
        assertEquals(2, crossover.numberOfGeneratedChildren());

        List<IntegerSolution> offspring = crossover.execute(Arrays.asList(parent0, parent1));
        assertEquals(Collections.nCopies(LENGTH, 2), offspring.get(0).variables());
        assertEquals(Collections.nCopies(LENGTH, 0), offspring.get(1).variables());
        // The parents are not modified
        assertEquals(Collections.nCopies(LENGTH, 0), parent0.variables());
        assertEquals(Collections.nCopies(LENGTH, 2), parent1.variables());
    }
}
