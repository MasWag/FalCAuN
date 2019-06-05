package org.group_mmm;

import com.google.common.collect.SortedSetMultimap;
import com.google.common.collect.TreeMultimap;
import de.learnlib.api.oracle.EquivalenceOracle;
import de.learnlib.api.query.DefaultQuery;
import net.automatalib.automata.transducers.MealyMachine;
import net.automatalib.commons.util.collections.CollectionsUtil;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import javax.annotation.ParametersAreNonnullByDefault;
import java.util.*;
import java.util.stream.Collectors;

public class HillClimbingEQOracle implements EquivalenceOracle.MealyEquivalenceOracle<String, String> {
    private static final Logger LOGGER = LoggerFactory.getLogger(HillClimbingEQOracle.class);
    private SimulinkMembershipOracleCost memOracle;
    private int length;
    private Random random;
    private int maxTests;

    private int generationSize;
    private int childrenSize;
    private int changeSize;

    HillClimbingEQOracle(SimulinkMembershipOracleCost memOracle,
                         int length,
                         Random random,
                         int maxTests,
                         int generationSize,
                         int childrenSize,
                         int changeSize) {
        this.memOracle = memOracle;
        this.length = length;
        this.random = random;
        this.maxTests = maxTests;
        this.generationSize = generationSize;
        this.childrenSize = childrenSize;
        this.changeSize = changeSize;
    }

    @Nullable
    @ParametersAreNonnullByDefault
    @Override
    public DefaultQuery<String, Word<String>> findCounterExample(MealyMachine<?, String, ?, String> hypothesis, Collection<? extends String> inputs) {
        // Fail fast on empty inputs
        if (inputs.isEmpty()) {
            LOGGER.warn("Passed empty set of inputs to equivalence oracle; no counterexample can be found!");
            return null;
        }
        int testSize = 0;
        ArrayList<Word<String>> currentSamples = new ArrayList<>(generationSize);
        final List<? extends String> symbolList = CollectionsUtil.randomAccessList(inputs);

        // Create the first generation
        for (int i = 0; i < generationSize; i++) {
            currentSamples.add(generateTestWord(symbolList));
        }

        do {
            SortedSetMultimap<Double, Word<String>> map = TreeMultimap.create((a, b) -> (int) (a - b), Comparator.comparingInt(Word::size));

            // Evaluate the current samples
            for (Word<String> sample : currentSamples) {
                DefaultQuery<String, Word<String>> query = new DefaultQuery<>(sample);
                Double result = memOracle.processQueryWithCost(query);
                Word<String> hypOutput = hypothesis.computeOutput(query.getInput());
                if (hypOutput != query.getOutput()) {
                    return query;
                }
                if (++testSize >= maxTests) {
                    return null;
                }
                map.put(result, sample);
            }

            List<Word<String>> goodSamples = map.entries().stream().limit(generationSize).map(Map.Entry::getValue).collect(Collectors.toList());

            // Construct next generation
            currentSamples = new ArrayList<>(generationSize * childrenSize);
            for (Word<String> sample : goodSamples) {
                for (int i = 0; i < childrenSize; i++) {
                    currentSamples.add(mutateWord(sample, symbolList));
                }
            }
        } while (testSize >= maxTests);

        return null;
    }

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

    private Word<String> mutateWord(Word<String> original, List<? extends String> symbolList) {
        final int numSyms = symbolList.size();
        final List<String> result = original.stream().collect(Collectors.toList());

        for (int i = 0; i < changeSize; i++) {
            final int changedIndex = random.nextInt(result.size() - 1);

            int symidx = random.nextInt(numSyms);
            String sym = symbolList.get(symidx);
            result.set(changedIndex, sym);
        }

        return Word.fromList(result);
    }
}
