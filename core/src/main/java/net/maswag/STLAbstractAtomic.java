package net.maswag;

import com.google.common.collect.Sets;
import javafx.util.Pair;
import net.automatalib.word.Word;

import java.util.*;
import java.util.stream.Collectors;

import static java.lang.Math.abs;

import net.maswag.TemporalLogic.STLCost;
import net.maswag.annotation.Sorted;

import javax.annotation.Nonnull;

/**
 * <p>STLAtomic class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
abstract public class STLAbstractAtomic extends AbstractTemporalLogic<List<Double>> implements STLCost {
    protected Operation op;
    protected int sigIndex;
    protected double comparator;
    protected Set<String> allAPs;

    /**
     * <p>Constructor for STLAtomic.</p>
     *
     * @param sigIndex   a int.
     * @param op         a {@link STLAbstractAtomic.Operation} object.
     * @param comparator a double.
     */
    public STLAbstractAtomic(int sigIndex, Operation op, double comparator) {
        this.sigIndex = sigIndex;
        this.comparator = comparator;
        this.op = op;
        this.nonTemporal = true;
    }

    public Set<String> getAllAPs(List<List<Character>> abstractValues, List<Character> largest) {
        if (this.allAPs == null) {
            List<Set<Character>> APList = new ArrayList<>(abstractValues.size());
            for (int i = 0; i < abstractValues.size(); i++) {
                APList.add(constructAllAPs(abstractValues, largest, i));
            }

            this.allAPs = cartesianProductCharacters(APList);
        }
        return allAPs;
    }

    public RoSI getRoSISingle(Word<List<Double>> signal) {
        List<Double> currentValue;

        if (signal.isEmpty()) {
            return new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY);
        }
        currentValue = signal.getSymbol(0);
        if (currentValue == null) {
            return new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY);
        }
        switch (op) {
            case lt:
                return new RoSI(comparator - currentValue.get(sigIndex));
            case gt:
                return new RoSI(currentValue.get(sigIndex) - comparator);
            case eq:
                return new RoSI(-abs(currentValue.get(sigIndex) - comparator));
            case ne:
                return new RoSI(abs(currentValue.get(sigIndex) - comparator));
            default:
                return null;
        }
    }

    abstract protected String getSignalName();

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        switch (op) {
            case lt:
                return String.format("%s(%d) < %f", getSignalName(), sigIndex, comparator);
            case eq:
                return String.format("%s(%d) == %f", getSignalName(), sigIndex, comparator);
            case gt:
                return String.format("%s(%d) > %f", getSignalName(), sigIndex, comparator);
            case ne:
                return String.format("%s(%d) != %f", getSignalName(), sigIndex, comparator);
        }
        return null;
    }

    protected void constructAtomicStrings(List<List<Double>> concreteValues,
                                          List<List<Character>> abstractValues,
                                          List<Character> largest) {
        if (this.satisfyingAtomicPropositions != null) {
            return;
        }

        List<Set<Character>> APList = new ArrayList<>(abstractValues.size());
        for (int i = 0; i < abstractValues.size(); i++) {
            if (i == sigIndex) {
                switch (op) {
                    case lt:
                        APList.add(constructSmallerAPs(concreteValues, abstractValues, largest, i, comparator));
                        break;
                    case eq:
                        APList.add(constructEqAPs(concreteValues, abstractValues, largest, i, comparator));
                        break;
                    case gt:
                        APList.add(constructLargerAPs(concreteValues, abstractValues, largest, i, comparator));
                        break;
                    case ne:
                        Set<Character> newAPs = constructAllAPs(abstractValues, largest, i);
                        newAPs.removeAll(constructEqAPs(concreteValues, abstractValues, largest, i, comparator));
                        APList.add(newAPs);
                }
            } else {
                APList.add(constructAllAPs(abstractValues, largest, i));
            }
        }

        this.satisfyingAtomicPropositions = cartesianProductCharacters(APList);
    }

    @Override
    public Set<String> getSatisfyingAtomicPropositions() {
        if (satisfyingAtomicPropositions == null) {
            constructSatisfyingAtomicPropositions();
        }
        return satisfyingAtomicPropositions;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toAbstractString() {
        if (this.satisfyingAtomicPropositions == null) {
            constructSatisfyingAtomicPropositions();
        }
        return this.satisfyingAtomicPropositions.stream().map(
                        s -> String.format("( %s == \"" + s + "\" )", getSignalName()))
                .collect(Collectors.joining(" || "));
    }

    /**
     * @param concreteValues The list of the concrete values of each signal
     *                       Each element of the list must be sorted in ascending order.
     */
    private Set<Character> constructSmallerAPs(List<List<Double>> concreteValues,
                                               List<List<Character>> abstractValues,
                                               List<Character> largest, int index, double threshold) {
        int bsResult = Collections.binarySearch(concreteValues.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? bsResult : (~bsResult - 1);
        Set<Character> resultAPs = new HashSet<>(abstractValues.get(index).subList(0, thresholdIndex + 1));
        if (bsResult < 0 && thresholdIndex == abstractValues.size() - 1) {
            resultAPs.add(largest.get(index));
        }

        return resultAPs;
    }

    /**
     * @param concreteValues The list of the concrete values of each signal
     *                       Each element of the list must be sorted in ascending order.
     */
    private Set<Character> constructLargerAPs(List<List<Double>> concreteValues,
                                              List<List<Character>> abstractValues,
                                              List<Character> largest, int index, double threshold) {
        int bsResult = Collections.binarySearch(concreteValues.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? bsResult : (~bsResult - 1);
        Set<Character> resultAPs = new HashSet<>(abstractValues.get(index).subList(thresholdIndex + 1, abstractValues.get(index).size()));

        resultAPs.add(largest.get(index));


        return resultAPs;
    }

    /**
     * @param concreteValues The list of the concrete values of each signal
     *                       Each element of the list must be sorted in ascending order.
     */
    private Set<Character> constructEqAPs(List<List<Double>> concreteValues,
                                          List<List<Character>> abstractValues,
                                          List<Character> largest, int index, double threshold) {
        int bsResult = Collections.binarySearch(concreteValues.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? bsResult : (~bsResult);
        Set<Character> resultAPs = new HashSet<>();
        if (!abstractValues.get(index).isEmpty()) {
            resultAPs.addAll(abstractValues.get(index).subList(thresholdIndex, thresholdIndex + 1));
        }
        if (abstractValues.get(index).isEmpty() ||
                (bsResult < 0 && thresholdIndex == abstractValues.size() - 1)) {
            resultAPs.add(largest.get(index));
        }
        assert resultAPs.size() == 1;

        return resultAPs;
    }

    /**
     * Construct the characters that represent the abstract values of the signal.
     *
     * @param abstractValues The list of the abstract values of each signal.
     * @param largest The largest value of each signal.
     *                If the signal is output signal this value is used to construct the atomic propositions.
     *                If the signal is input signal this value must be empty.
     * @param index The index of the signal
     */
    Set<Character> constructAllAPs(List<List<Character>> abstractValues, List<Character> largest, int index) {
        Set<Character> resultAPs = new HashSet<>(abstractValues.get(index));
        if (!largest.isEmpty()) {
            resultAPs.add(largest.get(index));
        }
        return resultAPs;
    }

    /**
     * Take the cartesian product of a list of sets of characters and return a set of strings by concatenating the characters.
     * <p>For example, if the input is [[a, b], [c, d]], the output will be {ac, ad, bc, bd}.</p>
     *
     * @param charList a list of sets of characters
     * @return a set of concatenated character combinations
     */
    static public @Nonnull Set<String> cartesianProductCharacters(@Nonnull List<Set<Character>> charList) {
        if (charList.isEmpty()) {
            return Collections.emptySet();
        }
        return Sets.cartesianProduct(charList).stream()
                .map(l -> l.stream().map(String::valueOf).collect(Collectors.joining()))
                .collect(Collectors.toSet());
    }

    /**
     * Decomposes a map with value Doubles into a pair of lists of keys and Doubles.
     *
     * @param map a map to Doubles
     * @param <T> the type of the keys
     * @return a pair of lists of keys and Doubles.
     * The first element is a list of keys and the second element is a list of values.
     * The returned lists are sorted in ascending order of the values.
     */
    static <T> Pair<List<T>, @Sorted List<Double>> decomposeMap(Map<T, Double> map) {
        List<Pair<T, Double>> pairs = new ArrayList<>(map.size());
        map.forEach((k, v) -> pairs.add(new Pair<>(k, v)));
        pairs.sort(Comparator.comparing(Pair::getValue));
        List<T> keys = new ArrayList<>(pairs.size());
        List<Double> values = new ArrayList<>(pairs.size());
        pairs.forEach(pair -> {
            keys.add(pair.getKey());
            values.add(pair.getValue());
        });
        return new Pair<>(keys, values);
    }

    /**
     * Decomposes a list of maps with value Doubles into a list of pair of lists of keys and Doubles.
     *
     * @param maps a list of maps to Doubles.
     * @param keyLists a list of lists of keys. The contents of this list will be cleared.
     * @param valueLists a list of lists of values. The contents of this list will be cleared.
     * @param <T> the type of the keys
     */
    static <T> void decomposeMapList(List<Map<T, Double>> maps, List<List<T>> keyLists, List<List<Double>> valueLists) {
        keyLists.clear();
        valueLists.clear();
        maps.forEach(map -> {
            Pair<List<T>, List<Double>> pair = decomposeMap(map);
            // The resulting lists must have the same size
            assert pair.getKey().size() == pair.getValue().size();
            // The resulting list must be sorted
            assert pair.getValue().stream().allMatch(c -> pair.getValue().get(0) <= c);
            keyLists.add(pair.getKey());
            valueLists.add(pair.getValue());
        });
        // The resulting lists must have the same size
        assert keyLists.size() == valueLists.size();
    }

    public enum Operation {
        lt,
        eq,
        gt,
        ne
    }
}
