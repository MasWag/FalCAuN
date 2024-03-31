package net.maswag;

import com.google.common.collect.SortedSetMultimap;
import com.google.common.collect.TreeMultimap;
import de.learnlib.oracle.EquivalenceOracle;
import de.learnlib.oracle.PropertyOracle;
import de.learnlib.query.DefaultQuery;
import lombok.Getter;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.common.util.collection.CollectionsUtil;
import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import javax.annotation.ParametersAreNonnullByDefault;
import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.primitives.Doubles.min;

/**
 * <p>Abstract AbstractSelectEQOracle class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public abstract class AbstractSelectEQOracle implements EquivalenceOracle.MealyEquivalenceOracle<String, String>,
        EvaluationCountable.MealyEquivalenceOracle<String, String> {
    private static final Logger LOGGER = LoggerFactory.getLogger(AbstractSelectEQOracle.class);
    Random random;
    int generationSize;
    int childrenSize;
    List<? extends String> symbolList;
    NumericMembershipOracleCost memOracle;
    private int length;
    private int maxTests;
    private boolean resetWord;
    private List<Word<String>> currentSamples = new ArrayList<>(generationSize);
    private PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle;
    @Getter
    private int evaluateCount = 0;

    AbstractSelectEQOracle(NumericMembershipOracleCost memOracle,
                           int length,
                           Random random,
                           int maxTests,
                           int generationSize,
                           int childrenSize,
                           boolean resetWord) {
        this.memOracle = memOracle;
        this.length = length;
        this.random = random;
        this.maxTests = maxTests;
        this.generationSize = generationSize;
        this.childrenSize = childrenSize;
        this.resetWord = resetWord;
    }

    AbstractSelectEQOracle(NumericMembershipOracleCost memOracle,
                           int length,
                           Random random,
                           int maxTests,
                           int generationSize,
                           int childrenSize,
                           boolean resetWord,
                           PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle) {
        this.memOracle = memOracle;
        this.length = length;
        this.random = random;
        this.maxTests = maxTests;
        this.generationSize = generationSize;
        this.childrenSize = childrenSize;
        this.resetWord = resetWord;
        this.ltlOracle = ltlOracle;
    }

    private void resetSamples() {
        currentSamples.clear();

        for (int i = 0; i < generationSize; i++) {
            currentSamples.add(generateTestWord(symbolList));
        }
    }

    private double minCost = Double.POSITIVE_INFINITY;

    /**
     * Returns whether the property is disproved i.e., whether it observed such an input that the cost function {@literal < 0}.
     *
     * @return whether the property is disproved.
     */
    private boolean isDisproved() {
        if (ltlOracle != null) {
            return ltlOracle.isDisproved();
        } else {
            return minCost < 0;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Nullable
    @ParametersAreNonnullByDefault
    @Override
    public DefaultQuery<String, Word<String>> findCounterExample(MealyMachine<?, String, ?, String> hypothesis, Collection<? extends String> inputs) {
        if (isDisproved()) {
            LOGGER.debug("A counterexample is already found!!");
            return null;
        }
        // Fail fast on empty inputs
        if (inputs.isEmpty()) {
            LOGGER.warn("Passed empty set of inputs to equivalence oracle; no counterexample can be found!");
            return null;
        }
        int testSize = 0;
        symbolList = CollectionsUtil.randomAccessList(inputs);

        if (resetWord || currentSamples.isEmpty()) {
            resetSamples();
        }

        do {
            SortedSetMultimap<Double, Word<String>> map = TreeMultimap.create(Comparator.comparingDouble(Double::doubleValue), Comparator.comparingInt(Word::size));

            // Evaluate the current samples
            for (Word<String> sample : currentSamples) {
                DefaultQuery<String, Word<String>> query = new DefaultQuery<>(sample);
                int oldCount = memOracle.getEvaluateCount();
                Double result = memOracle.processQueryWithCost(query);
                evaluateCount += memOracle.getEvaluateCount() - oldCount;
                Word<String> hypOutput = hypothesis.computeOutput(query.getInput());
                minCost = min(result, minCost);
                if (!Objects.equals(hypOutput, query.getOutput())) {
                    return query;
                }
                if (++testSize >= maxTests) {
                    return null;
                }
                map.put(result, sample);
            }
            LOGGER.debug("Test size: {}", testSize);

            List<Word<String>> goodSamples = map.entries().stream().limit(generationSize).map(Map.Entry::getValue).collect(Collectors.toList());

            // Construct next generation
            List<Word<String>> nextSamples = createNextGeneration(goodSamples);
            if (Objects.equals(nextSamples, currentSamples)) {
                resetSamples();
            } else {
                currentSamples = nextSamples;
            }
        } while (testSize < maxTests);

        return null;
    }

    /**
     * Generate one word of length {@code length} randomly
     *
     * @param symbolList The list of the possible symbols
     * @return the generated word
     */
    private Word<String> generateTestWord(List<? extends String> symbolList) {
        final int numSyms = symbolList.size();
        final WordBuilder<String> result = new WordBuilder<>(length);

        for (int j = 0; j < length; ++j) {
            int symidx = random.nextInt(numSyms);
            String sym = symbolList.get(symidx);
            result.append(sym);
        }

        return result.toWord();
    }

    abstract List<Word<String>> createNextGeneration(List<Word<String>> goodSamples);

}
