package net.maswag;

import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;
import net.maswag.TemporalLogic.STLCost;
import org.junit.jupiter.api.Test;

import java.util.*;

import static org.junit.jupiter.api.Assertions.assertEquals;

class STLAtomicTest {

    @Test
    void applyEmpty() {
        IOSignal<List<Double>> signal = new IODiscreteSignal<>(Word.epsilon(), Word.epsilon());
        STLCost formula = new STLOutputAtomic(0, STLOutputAtomic.Operation.lt, 10);
        double expected = Double.POSITIVE_INFINITY;
        double actual = formula.apply(signal);

        assertEquals(expected, actual);
    }

    @Test
    void ne() {
        WordBuilder<List<Double>> builder = new WordBuilder<>();
        builder.append(new ArrayList<>(Collections.singletonList(0.0)));
        Word<List<Double>> signal = builder.toWord();
        STLCost formula = new STLOutputAtomic(0, STLOutputAtomic.Operation.ne, 2);
        double expected = 2;
        double actual = formula.apply(new IODiscreteSignal<>(signal, signal));

        assertEquals(expected, actual);
    }

    @Test
    void getAllAPs() {
        STLOutputAtomic formula = new STLOutputAtomic(0, STLOutputAtomic.Operation.ne, 2);
        List<Map<Character, Double>> abstractOutputs = new ArrayList<>();
        List<Character> largest = List.of('d', 'c', 'b');
        abstractOutputs.add(Map.of('a', 1.0, 'b', 2.0, 'c', 3.0));
        abstractOutputs.add(Map.of('a', 1.0, 'b', 2.0));
        abstractOutputs.add(Map.of('a', 1.0));
        formula.setAtomic(abstractOutputs, largest);
        Set<String> expected = Set.of("aaa", "aab", "aba", "abb", "aca", "acb", "baa", "bab", "bba", "bbb", "bca", "bcb", "caa", "cab", "cba", "cbb", "cca", "ccb", "daa", "dab", "dba", "dbb", "dca", "dcb");
        Set<String> actual = formula.getAllAPs();

        assertEquals(expected, actual);
    }

    @Test
    void cartesianProductCharacters() {
        List<Set<Character>> APList = new ArrayList<>();
        APList.add(Set.of('a', 'b'));
        APList.add(Set.of('c', 'd'));
        APList.add(Set.of('e', 'f'));
        Set<String> expected = Set.of("ace", "acf", "ade", "adf", "bce", "bcf", "bde", "bdf");
        Set<String> actual = STLAbstractAtomic.cartesianProductCharacters(APList);

        assertEquals(expected, actual);
    }
}