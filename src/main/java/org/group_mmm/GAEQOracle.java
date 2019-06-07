package org.group_mmm;

import net.automatalib.words.Word;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

class GAEQOracle extends MutateSelectEQOracle {
    private double crossoverProb;
    private double mutationProb;

    GAEQOracle(SimulinkMembershipOracleCost memOracle, int length, Random random, int maxTests, int generationSize, int childrenSize, int changeSize, double crossoverProb, double mutationProb, boolean resetWord) {
        super(memOracle, length, random, maxTests, generationSize, childrenSize, changeSize, resetWord);
        this.crossoverProb = crossoverProb;
        this.mutationProb = mutationProb;
    }

    @Override
    protected List<Word<String>> createNextGeneration(List<Word<String>> goodWords) {
        ArrayList<Word<String>> nextGeneration = new ArrayList<>(generationSize * childrenSize);

        for (Word<String> goodWord : goodWords) {
            for (int i = 0; i < childrenSize; i++) {
                if (Math.random() <= crossoverProb) {
                    // crossover
                    final Word<String> anotherWord = goodWords.get(random.nextInt(goodWords.size()));
                    ArrayList<String> g1 = new ArrayList<>(goodWord.size());
                    ArrayList<String> g2 = new ArrayList<>(goodWord.size());
                    assert goodWord.size() == anotherWord.size();
                    for (int j = 0; j < goodWord.size(); j++) {
                        if (Math.random() >= 0.5) {
                            g1.add(goodWord.getSymbol(j));
                            g2.add(anotherWord.getSymbol(j));
                        } else {
                            g1.add(anotherWord.getSymbol(j));
                            g2.add(goodWord.getSymbol(j));
                        }
                    }
                    goodWord = Word.fromList(g1);
                    nextGeneration.add(Word.fromList(g2));
                }
                if (Math.random() <= mutationProb) {
                    // mutation
                    goodWord = mutateWord(goodWord, symbolList);
                }
                nextGeneration.add(goodWord);
            }
        }
        return nextGeneration;
    }
}