package net.maswag;

import de.learnlib.oracle.PropertyOracle;
import de.learnlib.query.DefaultQuery;
import net.automatalib.word.Word;

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
    private double iteration = 0.0;

    /**
     * <p>Constructor for SAEQOracle.</p>
     *
     * @param memOracle a {@link NumericMembershipOracleCost} object.
     * @param length a int.
     * @param random a {@link java.util.Random} object.
     * @param maxTests a int.
     * @param generationSize a int.
     * @param childrenSize a int.
     * @param resetWord a boolean.
     * @param alpha a double.
     */
    public SAEQOracle(NumericMembershipOracleCost memOracle, int length, Random random, int maxTests, int generationSize, int childrenSize, boolean resetWord, double alpha) {
        super(memOracle, length, random, maxTests, generationSize, childrenSize, resetWord);
        maxIteration = maxTests / (generationSize * childrenSize);
        this.alpha = alpha;
    }

    SAEQOracle(NumericMembershipOracleCost memOracle, int length, Random random, int maxTests, int generationSize, int childrenSize, boolean resetWord, double alpha, PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle) {
        super(memOracle, length, random, maxTests, generationSize, childrenSize, resetWord, ltlOracle);
        maxIteration = maxTests / (generationSize * childrenSize);
        this.alpha = alpha;
    }

    /** {@inheritDoc} */
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
     * We followed the algorithm in https://ja.wikipedia.org/wiki/%E7%84%BC%E3%81%8D%E3%81%AA%E3%81%BE%E3%81%97%E6%B3%95 .
     */
    private boolean shouldPick(double srcCost, double dstCost) {
        if (srcCost >= dstCost) {
            return true;
        } else {
            double temperature = Math.pow(alpha, iteration / maxIteration);
            return Math.exp((srcCost - dstCost) / temperature) >= this.random.nextDouble();
        }
    }

    private double onlyEval(Word<String> input) {
        DefaultQuery<String, Word<String>> query = new DefaultQuery<>(input);
        return this.memOracle.processQueryWithCost(query);
    }
}
