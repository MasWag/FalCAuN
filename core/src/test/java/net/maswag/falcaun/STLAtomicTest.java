package net.maswag.falcaun;

import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;
import net.maswag.falcaun.TemporalLogic.STLCost;
import org.junit.jupiter.api.Test;

import java.util.*;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.*;

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
    void getAllAPsInput() {
        STLInputAtomic formula = new STLInputAtomic(0, STLOutputAtomic.Operation.ne, 2);
        List<Map<Character, Double>> inputMapper = new ArrayList<>();
        inputMapper.add(Map.of('a', 1.0, 'b', 2.0, 'c', 3.0));
        inputMapper.add(Map.of('a', 1.0, 'b', 2.0));
        inputMapper.add(Map.of('a', 1.0));
        formula.setInputMapper(inputMapper);
        Set<String> expected = Set.of("aaa", "aba", "baa", "bba", "caa", "cba");
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

    @Test
    void toAbstractStringOutput() {
        STLOutputAtomic formula = new STLOutputAtomic(0, STLOutputAtomic.Operation.ne, 2.0);
        List<Map<Character, Double>> abstractOutputs = new ArrayList<>();
        List<Character> largest = List.of('d', 'c', 'b');
        abstractOutputs.add(Map.of('a', 1.0, 'b', 2.0, 'c', 3.0));
        abstractOutputs.add(Map.of('a', 1.0, 'b', 2.0));
        abstractOutputs.add(Map.of('a', 1.0));
        formula.setAtomic(abstractOutputs, largest);
        Set<String> expected = Set.of("aaa", "aab", "aba", "abb", "aca", "acb", "caa", "cab", "cba", "cbb", "cca", "ccb", "daa", "dab", "dba", "dbb", "dca", "dcb");
        // We do an ad hoc parsing of the abstract string to get the atomic propositions
        Set<String> actual = Arrays.stream(formula.toAbstractString()
                .split("\"")).filter(s -> s.length() == 3).collect(Collectors.toSet());

        assertEquals(expected, actual);

        // The abstract string should start with "( output =="
        assertTrue(formula.toAbstractString().startsWith("( output =="));
        // The abstract string must not contain "input"
        assertFalse(formula.toAbstractString().contains("input"));
    }

    @Test
    void toAbstractStringInput() {
        STLInputAtomic formula = new STLInputAtomic(0, STLOutputAtomic.Operation.ne, 2);
        List<Map<Character, Double>> inputMapper = new ArrayList<>();
        inputMapper.add(Map.of('a', 1.0, 'b', 2.0, 'c', 3.0));
        inputMapper.add(Map.of('a', 1.0, 'b', 2.0));
        inputMapper.add(Map.of('a', 1.0));
        formula.setInputMapper(inputMapper);
        Set<String> expected = Set.of("aaa", "aba", "caa", "cba");
        // We do an ad hoc parsing of the abstract string to get the atomic propositions
        Set<String> actual = Arrays.stream(formula.toAbstractString()
                .split("\"")).filter(s -> s.length() == 3).collect(Collectors.toSet());

        assertEquals(expected, actual);

        // The abstract string should start with "( input =="
        assertTrue(formula.toAbstractString().startsWith("( input =="));
        // The abstract string must not contain "output"
        assertFalse(formula.toAbstractString().contains("output"));
    }

    @Test
    void toAbstractStringOutputDisjunction() {
        List<Map<Character, Double>> inputMapper = new ArrayList<>();
        inputMapper.add(Map.of('a', 1.0, 'b', 2.0, 'c', 3.0));
        inputMapper.add(Map.of('a', 1.0, 'b', 2.0));
        inputMapper.add(Map.of('a', 1.0));

        STLInputAtomic formula1 = new STLInputAtomic(0, STLOutputAtomic.Operation.ne, 2);
        formula1.setInputMapper(inputMapper);
        STLInputAtomic formula2 = new STLInputAtomic(1, STLOutputAtomic.Operation.ne, 2);
        formula2.setInputMapper(inputMapper);
        STLCost formula = new TemporalOr.STLOr(formula1, formula2);

        Set<String> expected = Set.of("aaa", "aba", "baa", "caa", "cba");
        // We do an ad hoc parsing of the abstract string to get the atomic propositions
        Set<String> actual = Arrays.stream(formula.toAbstractString()
                .split("\"")).filter(s -> s.length() == 3).collect(Collectors.toSet());

        assertEquals(expected, actual);

        // The abstract string should start with "( input =="
        assertTrue(formula.toAbstractString().startsWith("( input =="));
        // The abstract string must not contain "output"
        assertFalse(formula.toAbstractString().contains("output"));
    }
}