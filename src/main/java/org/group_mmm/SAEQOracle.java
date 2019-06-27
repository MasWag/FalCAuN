package org.group_mmm;

import de.learnlib.api.oracle.PropertyOracle;
import de.learnlib.api.query.DefaultQuery;
import net.automatalib.words.Word;

import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;

/**
 * Answer the Equivalence query by simulated annealing
 *
 * @author Masaki Waga
 */
public class SAEQOracle extends HillClimbingEQOracle {
    private double alpha;
    private int maxIteration;
    private int iteration = 0;

    public SAEQOracle(SimulinkMembershipOracleCost memOracle, int length, Random random, int maxTests, int generationSize, int childrenSize, boolean resetWord, double alpha) {
        super(memOracle, length, random, maxTests, generationSize, childrenSize, resetWord);
        maxIteration = maxTests / (generationSize * childrenSize);
        this.alpha = alpha;
    }

    SAEQOracle(SimulinkMembershipOracleCost memOracle, int length, Random random, int maxTests, int generationSize, int childrenSize, boolean resetWord, double alpha, PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle) {
        super(memOracle, length, random, maxTests, generationSize, childrenSize, resetWord, ltlOracle);
        maxIteration = maxTests / (generationSize * childrenSize);
        this.alpha = alpha;
    }

    @Override
    protected List<Word<String>> createNextGeneration(List<Word<String>> goodSamples) {
        iteration++;
        return goodSamples.stream().flatMap(src -> {
            double srcCost = onlyEval(src);
            return neighborhoodStream(src)
                    .filter(dst -> shouldPick(srcCost, onlyEval(dst))).limit(this.childrenSize);
        }).collect(Collectors.toList());
    }

    /**
     * @param srcCost the cost of src
     * @param dstCost the cost of dst
     * @return if we should transit from src to dst.
     */
    private boolean shouldPick(double srcCost, double dstCost) {
        if (srcCost >= dstCost) {
            return true;
        } else {
            double temperature = Math.pow(alpha, iteration * 1.0 / maxIteration);
            return (srcCost - dstCost) / temperature >= Math.log(this.random.nextDouble());
        }
    }

    private double onlyEval(Word<String> input) {
        DefaultQuery<String, Word<String>> query = new DefaultQuery<>(input);
        return this.memOracle.processQueryWithCost(query);
    }
}
