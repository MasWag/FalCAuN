package org.group_mmm;

import de.learnlib.api.oracle.PropertyOracle;
import net.automatalib.words.Word;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

/**
 * <p>HillClimbingEQOracle class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class HillClimbingEQOracle extends AbstractSelectEQOracle {
    HillClimbingEQOracle(SimulinkMembershipOracleCost memOracle, int length, Random random, int maxTests, int generationSize, int childrenSize, boolean resetWord) {
        super(memOracle, length, random, maxTests, generationSize, childrenSize, resetWord);
    }

    HillClimbingEQOracle(SimulinkMembershipOracleCost memOracle, int length, Random random, int maxTests, int generationSize, int childrenSize, boolean resetWord, PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle) {
        super(memOracle, length, random, maxTests, generationSize, childrenSize, resetWord, ltlOracle);
    }

    /** {@inheritDoc} */
    @Override
    protected List<Word<String>> createNextGeneration(List<Word<String>> goodSamples) {
        return goodSamples.stream().flatMap(w -> neighborhoodStream(w).limit(this.childrenSize)).collect(Collectors.toList());
    }

    /**
     * Generate the stream returning the neighborhood of the given word
     *
     * @param input the input word
     * @return the stream returning the neighborhood of the given word
     */
    Stream<Word<String>> neighborhoodStream(Word<String> input) {
        List<Integer> indices = IntStream.range(0, input.length()).boxed().collect(Collectors.toList());
        Collections.shuffle(indices);
        return indices.stream().flatMap(
                index -> {
                    List<String> symbolList = new ArrayList<>(this.symbolList);
                    Collections.shuffle(symbolList);
                    return symbolList.stream().filter(s -> !s.equals(input.getSymbol(index))).map(s ->
                    {
                        List<String> tmp = input.stream().collect(Collectors.toList());
                        tmp.set(index, s);
                        return Word.fromList(tmp);
                    });
                });
    }
}
