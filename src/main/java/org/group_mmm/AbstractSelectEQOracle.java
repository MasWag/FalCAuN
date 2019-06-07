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

public abstract class AbstractSelectEQOracle implements EquivalenceOracle.MealyEquivalenceOracle<String, String> {
    private static final Logger LOGGER = LoggerFactory.getLogger(AbstractSelectEQOracle.class);
    Random random;
    int generationSize;
    int childrenSize;
    List<? extends String> symbolList;
    private SimulinkMembershipOracleCost memOracle;
    private int length;
    private int maxTests;
    private boolean resetWord;
    private List<Word<String>> currentSamples = new ArrayList<>(generationSize);

    AbstractSelectEQOracle(SimulinkMembershipOracleCost memOracle,
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
        symbolList = CollectionsUtil.randomAccessList(inputs);

        if (resetWord || currentSamples.isEmpty()) {
            // Create the first generation
            for (int i = 0; i < generationSize; i++) {
                currentSamples.add(generateTestWord(symbolList));
            }
        }

        do {
            SortedSetMultimap<Double, Word<String>> map = TreeMultimap.create(Comparator.comparingDouble(Double::doubleValue), Comparator.comparingInt(Word::size));

            // Evaluate the current samples
            for (Word<String> sample : currentSamples) {
                DefaultQuery<String, Word<String>> query = new DefaultQuery<>(sample);
                Double result = memOracle.processQueryWithCost(query);
                Word<String> hypOutput = hypothesis.computeOutput(query.getInput());
                if (!Objects.equals(hypOutput, query.getOutput())) {
                    return query;
                }
                if (++testSize >= maxTests) {
                    return null;
                }
                map.put(result, sample);
            }

            List<Word<String>> goodSamples = map.entries().stream().limit(generationSize).map(Map.Entry::getValue).collect(Collectors.toList());

            // Construct next generation
            currentSamples = createNextGeneration(goodSamples);
        } while (testSize < maxTests);

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

    abstract List<Word<String>> createNextGeneration(List<Word<String>> goodSamples);

}
