package org.group_mmm;

import net.automatalib.words.Word;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;

public class MutateSelectEQOracle extends AbstractSelectEQOracle {
    private int changeSize;

    MutateSelectEQOracle(SimulinkMembershipOracleCost memOracle, int length, Random random, int maxTests, int generationSize, int childrenSize, boolean resetWord, int changeSize) {
        super(memOracle, length, random, maxTests, generationSize, childrenSize, resetWord);
        this.changeSize = changeSize;
    }

    protected List<Word<String>> createNextGeneration(List<Word<String>> goodSamples) {
        ArrayList<Word<String>> nextGeneration = new ArrayList<>(generationSize * childrenSize);

        for (Word<String> sample : goodSamples) {
            for (int i = 0; i < childrenSize; i++) {
                nextGeneration.add(mutateWord(sample, symbolList));
            }
        }
        return nextGeneration;
    }

    Word<String> mutateWord(Word<String> original, List<? extends String> symbolList) {
        final int numSyms = symbolList.size();
        final List<String> result = original.stream().collect(Collectors.toList());

        for (int i = 0; i < changeSize; i++) {
            final int changedIndex = random.nextInt(result.size());

            int symidx = random.nextInt(numSyms);
            String sym = symbolList.get(symidx);
            result.set(changedIndex, sym);
        }

        return Word.fromList(result);
    }
}
