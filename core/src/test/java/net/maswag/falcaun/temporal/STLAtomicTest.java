package net.maswag.falcaun.temporal;

import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;
import net.maswag.falcaun.abstraction.InputMapper;
import net.maswag.falcaun.abstraction.OutputMapper;
import net.maswag.falcaun.abstraction.SignalAdapter;
import net.maswag.falcaun.signal.IODiscreteSignal;
import net.maswag.falcaun.signal.IOSignal;
import net.maswag.falcaun.signal.IOSignalPiece;
import net.maswag.falcaun.temporal.TemporalLogic.STLCost;

import org.junit.jupiter.api.Test;

import java.util.*;
import java.util.stream.Collectors;
import org.apache.commons.lang3.tuple.Pair;

import static org.junit.jupiter.api.Assertions.*;

class STLAtomicTest {

    @Test
    void applyEmpty() {
        IOSignal<List<Double>> signal = new IODiscreteSignal<>(Word.epsilon(), Word.epsilon());
        STLCost formula = new STLOutputAtomic(0, STLOutputAtomic.Operation.le, 10);
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
        STLInputAtomic formula = new STLInputAtomic(0, STLInputAtomic.Operation.ne, 2);
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

        STLInputAtomic formula1 = new STLInputAtomic(0, STLInputAtomic.Operation.ne, 2);
        formula1.setInputMapper(inputMapper);
        STLInputAtomic formula2 = new STLInputAtomic(1, STLInputAtomic.Operation.ne, 2);
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

    @Test
    void toAbstractStringInputPositive() {
        List<Map<Character, Double>> inputMapper = new ArrayList<>();
        inputMapper.add(Map.of('a', 1.0, 'b', 2.0));
        inputMapper.add(Map.of('x', 1.0));
        inputMapper.add(Map.of('y', 0.0));

        List<Pair<STLInputAtomic, Set<String>>> testCases = List.of(
            Pair.of(new STLInputAtomic(0, STLInputAtomic.Operation.le, 0.5), Set.of()),
            Pair.of(new STLInputAtomic(0, STLInputAtomic.Operation.le, 1.0), Set.of("axy")),
            Pair.of(new STLInputAtomic(0, STLInputAtomic.Operation.le, 1.5), Set.of("axy")),
            Pair.of(new STLInputAtomic(0, STLInputAtomic.Operation.le, 2.0), Set.of("axy", "bxy")),
            Pair.of(new STLInputAtomic(0, STLInputAtomic.Operation.le, 2.5), Set.of("axy", "bxy")),
            Pair.of(new STLInputAtomic(0, STLInputAtomic.Operation.gt, 0.5), Set.of("axy", "bxy")),
            Pair.of(new STLInputAtomic(0, STLInputAtomic.Operation.gt, 1.0), Set.of("bxy")),
            Pair.of(new STLInputAtomic(0, STLInputAtomic.Operation.gt, 1.5), Set.of("bxy")),
            Pair.of(new STLInputAtomic(0, STLInputAtomic.Operation.gt, 2.0), Set.of()),
            Pair.of(new STLInputAtomic(0, STLInputAtomic.Operation.gt, 2.5), Set.of()),
            Pair.of(new STLInputAtomic(0, STLInputAtomic.Operation.eq, 1.0), Set.of("axy")),
            Pair.of(new STLInputAtomic(0, STLInputAtomic.Operation.eq, 2.0), Set.of("bxy"))
        );

        for (Pair<STLInputAtomic, Set<String>> test : testCases) {
            var formula = test.getLeft();
            formula.setInputMapper(inputMapper);

            // We do an ad hoc parsing of the abstract string to get the atomic propositions
            var actual = Arrays.stream(formula.toAbstractString()
                    .split("\"")).filter(s -> s.length() == inputMapper.size()).collect(Collectors.toSet());
            var expected = test.getRight();
            assertEquals(expected, actual);
        }
    }

    @Test
    void toAbstractStringInputNegative() {
        List<Map<Character, Double>> inputMapper = new ArrayList<>();
        inputMapper.add(Map.of('a', 1.0, 'b', 2.0));
        inputMapper.add(Map.of('x', 1.0));
        inputMapper.add(Map.of('y', 0.0));

        List<STLInputAtomic> testCases = List.of(
            new STLInputAtomic(0, STLInputAtomic.Operation.eq, 0.5),
            new STLInputAtomic(0, STLInputAtomic.Operation.eq, 1.5),
            new STLInputAtomic(0, STLInputAtomic.Operation.eq, 2.5)
        );

        for (STLInputAtomic formula : testCases) {
            formula.setInputMapper(inputMapper);
            assertThrows(RuntimeException.class, () -> formula.toAbstractString());
        }
    }

    @Test
    void toAbstractStringOutputPositive() {
        List<Map<Character, Double>> outputMapper = new ArrayList<>();
        List<Character> largest = List.of('c', 'x', 'y');
        outputMapper.add(Map.of('a', 1.0, 'b', 2.0));
        outputMapper.add(Map.of());
        outputMapper.add(Map.of());

        List<Pair<STLOutputAtomic, Set<String>>> testCases = List.of(
            Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.le, 0.5), Set.of()),
            Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.le, 1.0), Set.of("axy")),
            Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.le, 1.5), Set.of("axy")),
            Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.le, 2.0), Set.of("axy", "bxy")),
            Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.le, 2.5), Set.of("axy", "bxy")),
            Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 0.5), Set.of("axy", "bxy", "cxy")),
            Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 1.0), Set.of("bxy", "cxy")),
            Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 1.5), Set.of("bxy", "cxy")),
            Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 2.0), Set.of("cxy")),
            Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 2.5), Set.of("cxy")),
            Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.eq, 0.5), Set.of("axy")),
            Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.eq, 1.0), Set.of("axy")),
            Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.eq, 1.5), Set.of("bxy")),
            Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.eq, 2.0), Set.of("bxy"))
            );

        for (Pair<STLOutputAtomic, Set<String>> test : testCases) {
            var formula = test.getLeft();
            formula.setAtomic(outputMapper, largest);

            // We do an ad hoc parsing of the abstract string to get the atomic propositions
            var actual = Arrays.stream(formula.toAbstractString()
                    .split("\"")).filter(s -> s.length() == outputMapper.size()).collect(Collectors.toSet());
            var expected = test.getRight();
            assertEquals(expected, actual);
        }
    }

    @Test
    void toAbstractStringOutputNegative() {
        List<Map<Character, Double>> outputMapper = new ArrayList<>();
        List<Character> largest = List.of('c', 'x', 'y');
        outputMapper.add(Map.of('a', 1.0, 'b', 2.0));

        List<STLOutputAtomic> testCases = List.of(
            new STLOutputAtomic(0, STLOutputAtomic.Operation.eq, 2.5)
        );

        for (STLOutputAtomic formula : testCases) {
            formula.setAtomic(outputMapper, largest);
            assertThrows(RuntimeException.class, () -> formula.toAbstractString());
        }
    }

    @Test
    void eval() {
        List<Map<Character, Double>> outputMapper = new ArrayList<>();
        outputMapper.add(Map.of('a', 1.0, 'b', 2.0));
        List<Character> largest = List.of('c');
        SignalAdapter adapter = new SignalAdapter(
                InputMapper.make(Collections.singletonList(Collections.singletonList(1.0))),
                new OutputMapper(outputMapper, largest));

        List<Pair<STLOutputAtomic, Boolean>> tests = List.of(
                // le is non-strict: it holds at the threshold
                Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.le, 1.0), true),
                Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.le, 2.0), true),
                Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 1.0), false),
                Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 2.0), false),
                Pair.of(new STLOutputAtomic(0, STLOutputAtomic.Operation.eq, 1.0), true)
        );

        for (Pair<STLOutputAtomic, Boolean> test : tests) {
            STLOutputAtomic formula = test.getLeft();
            formula.setAtomic(outputMapper, largest);
            IOSignalPiece<List<Double>> piece = new IOSignalPiece<>(
                    Collections.singletonList(1.0),
                    Collections.singletonList(1.0));
            String asString = adapter.mapOutput(piece);
            assertEquals("a", asString);

            // We do an ad hoc parsing of the abstract string to get the atomic propositions
            Set<String> satisfyingString = Arrays.stream(formula.toAbstractString()
                    .split("\"")).filter(s -> s.length() == outputMapper.size()).collect(Collectors.toSet());
            var expected = test.getRight();
            assertEquals(expected, satisfyingString.contains(asString));
        }
    }

    @Test
    void toAbstractLTLStringOutput() {
        STLOutputAtomic formula = new STLOutputAtomic(0, STLOutputAtomic.Operation.ne, 2.0);
        List<Map<Character, Double>> abstractOutputs = new ArrayList<>();
        List<Character> largest = List.of('d', 'c', 'b');
        abstractOutputs.add(Map.of('a', 1.0, 'b', 2.0, 'c', 3.0));
        abstractOutputs.add(Map.of('a', 1.0, 'b', 2.0));
        abstractOutputs.add(Map.of('a', 1.0));
        formula.setAtomic(abstractOutputs, largest);
        Set<String> satisfyingAPList = Set.of("aaa", "aab", "aba", "abb", "aca", "acb", "caa", "cab", "cba", "cbb", "cca", "ccb", "daa", "dab", "dba", "dbb", "dca", "dcb");
        Map<String, String> mapper1 =
            Map.of("aaa", "aaa",
                   "aab", "aaa",
                   "aba", "aba",
                   "abb", "aba",
                   "aca", "aaa",
                   "acb", "acb",
                   "caa", "caa",
                   "cab", "aaa",
                   "cba", "cba"); 
        Map<String, String> mapper2 =
            Map.of("cbb", "cbb",
                   "cca", "cbb",
                   "ccb", "aaa",
                   "daa", "daa",
                   "dab", "dab",
                   "dba", "daa",
                   "dbb", "dbb",
                   "dca", "aba",
                   "dcb", "cba");
        Map<String, String> mapper = new HashMap<>();
        mapper.putAll(mapper1);
        mapper.putAll(mapper2);
        Set<String> expected = satisfyingAPList.stream().map(ap -> mapper.get(ap)).collect(Collectors.toSet());

        // We do an ad hoc parsing of the abstract string to get the atomic propositions
        Set<String> actual = Arrays.stream(formula.toAbstractLTLString(mapper)
                .split("\"")).filter(s -> s.length() == 3).collect(Collectors.toSet());

        assertEquals(expected, actual);

        // The abstract string should start with "( output =="
        assertTrue(formula.toAbstractString().startsWith("( output =="));
        // The abstract string must not contain "input"
        assertFalse(formula.toAbstractString().contains("input"));
    }

    /**
     * Returns the satisfying atomic propositions of a single-signal atomic formula.
     */
    private static Set<String> satisfyingAPs(STLAbstractAtomic formula) {
        return Arrays.stream(formula.toAbstractString().split("\""))
                .filter(str -> str.length() == 1).collect(Collectors.toSet());
    }

    private static IOSignal<List<Double>> singleStepSignal(double input, double output) {
        return new IODiscreteSignal<>(Word.fromLetter(List.of(input)), Word.fromLetter(List.of(output)));
    }

    /**
     * Regression test for #305: at exact mapper thresholds and their neighbors,
     * the input APs of {@literal <=} and {@literal >} are complementary.
     */
    @Test
    void inputLeAndGtAreComplementary() {
        List<Map<Character, Double>> inputMapper = List.of(Map.of('a', 1.0, 'b', 2.0));
        Map<Character, Double> letterToValue = inputMapper.get(0);
        for (double threshold : List.of(0.5, 1.0, 1.5, 2.0, 2.5)) {
            STLInputAtomic le = new STLInputAtomic(0, STLAbstractAtomic.Operation.le, threshold);
            STLInputAtomic gt = new STLInputAtomic(0, STLAbstractAtomic.Operation.gt, threshold);
            le.setInputMapper(inputMapper);
            gt.setInputMapper(inputMapper);
            Set<String> leAPs = satisfyingAPs(le);
            Set<String> gtAPs = satisfyingAPs(gt);

            assertTrue(Collections.disjoint(leAPs, gtAPs), "threshold " + threshold);
            Set<String> union = new HashSet<>(leAPs);
            union.addAll(gtAPs);
            assertEquals(le.getAllAPs(), union, "threshold " + threshold);

            // The abstract satisfaction coincides with the concrete Boolean semantics
            for (Map.Entry<Character, Double> entry : letterToValue.entrySet()) {
                String letter = String.valueOf(entry.getKey());
                double value = entry.getValue();
                assertEquals(value <= threshold, leAPs.contains(letter), letter + " <= " + threshold);
                assertEquals(value > threshold, gtAPs.contains(letter), letter + " > " + threshold);
            }
        }
    }

    /**
     * Regression test for #305: at exact mapper thresholds and their neighbors,
     * the output APs of {@literal <=} and {@literal >} are complementary, and
     * at mapped thresholds they are consistent with the concrete Boolean semantics.
     */
    @Test
    void outputLeAndGtAreComplementary() {
        List<Map<Character, Double>> outputMapper = List.of(Map.of('a', 1.0, 'b', 2.0));
        List<Character> largest = List.of('c');
        SignalAdapter adapter = new SignalAdapter(
                InputMapper.make(Collections.singletonList(Collections.singletonList(1.0))),
                new OutputMapper(outputMapper, largest));
        List<Double> mappedThresholds = List.of(1.0, 2.0);
        for (double threshold : List.of(0.5, 1.0, 1.5, 2.0, 2.5)) {
            STLOutputAtomic le = new STLOutputAtomic(0, STLAbstractAtomic.Operation.le, threshold);
            STLOutputAtomic gt = new STLOutputAtomic(0, STLAbstractAtomic.Operation.gt, threshold);
            le.setAtomic(outputMapper, largest);
            gt.setAtomic(outputMapper, largest);
            Set<String> leAPs = satisfyingAPs(le);
            Set<String> gtAPs = satisfyingAPs(gt);

            assertTrue(Collections.disjoint(leAPs, gtAPs), "threshold " + threshold);
            Set<String> union = new HashSet<>(leAPs);
            union.addAll(gtAPs);
            assertEquals(Set.of("a", "b", "c"), union, "threshold " + threshold);

            if (!mappedThresholds.contains(threshold)) {
                // Comparisons with thresholds absent from the mapper are approximated (out of scope of #305).
                continue;
            }
            for (double value : List.of(0.5, 1.0, 1.5, 2.0, 2.5)) {
                String letter = adapter.mapOutput(new IOSignalPiece<>(List.of(1.0), List.of(value)));
                assertEquals(value <= threshold, leAPs.contains(letter), value + " <= " + threshold);
                assertEquals(value > threshold, gtAPs.contains(letter), value + " > " + threshold);
            }
        }
    }

    /**
     * Regression test for #305: the robustness of {@literal <=} and {@literal >} is unchanged,
     * in particular, both are zero at equality.
     */
    @Test
    void leRobustnessAtBoundary() {
        for (double value : List.of(0.5, 1.0, 1.5)) {
            IOSignal<List<Double>> signal = singleStepSignal(value, value);
            List<STLAbstractAtomic> leFormulas = List.of(
                    new STLInputAtomic(0, STLAbstractAtomic.Operation.le, 1.0),
                    new STLOutputAtomic(0, STLAbstractAtomic.Operation.le, 1.0));
            List<STLAbstractAtomic> gtFormulas = List.of(
                    new STLInputAtomic(0, STLAbstractAtomic.Operation.gt, 1.0),
                    new STLOutputAtomic(0, STLAbstractAtomic.Operation.gt, 1.0));
            for (STLAbstractAtomic formula : leFormulas) {
                RoSI rosi = formula.getRoSI(signal);
                assertEquals(1.0 - value, rosi.lowerBound, formula + " at " + value);
                assertEquals(1.0 - value, rosi.upperBound, formula + " at " + value);
            }
            for (STLAbstractAtomic formula : gtFormulas) {
                RoSI rosi = formula.getRoSI(signal);
                assertEquals(value - 1.0, rosi.lowerBound, formula + " at " + value);
                assertEquals(value - 1.0, rosi.upperBound, formula + " at " + value);
            }
        }
    }
}
