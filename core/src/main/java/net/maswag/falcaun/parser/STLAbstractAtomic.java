package net.maswag.falcaun.parser;

import static java.lang.Math.abs;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import javax.annotation.Nonnull;

import net.maswag.falcaun.annotation.Sorted;

import org.apache.commons.math3.util.Pair;

import com.google.common.collect.Sets;

import net.automatalib.word.Word;

/**
 * <p>STLAtomic class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
abstract public class STLAbstractAtomic extends AbstractTemporalLogic<List<Double>> implements TemporalLogic.STLCost {
    protected Operation op;
    protected int sigIndex;
    protected double comparator;
    protected Set<String> allAPs;

    /**
     * <p>Constructor for STLAtomic.</p>
     *
     * @param sigIndex   An index of signals
     * @param op         The comparison operator {@link STLAbstractAtomic.Operation}
     * @param comparator The value to compare against
     */
    public STLAbstractAtomic(int sigIndex, Operation op, double comparator) {
        this.sigIndex = sigIndex;
        this.comparator = comparator;
        this.op = op;
        this.nonTemporal = true;
    }

    /**
     * {@inheritDoc}
     *
     * @param signalSize the length of the signal greater than this.sigIndex
     */
    protected Set<String> getAllAPs(int signalSize) {
        if (this.allAPs == null) {
            List<Set<Character>> APList = new ArrayList<>(signalSize);
            for (int i = 0; i < signalSize; i++) {
                APList.add(constructAllAPs(i));
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

    /**
     * @param signalSize the length of the signal
     */
    protected void constructAtomicStrings(int signalSize) {
        if (this.satisfyingAtomicPropositions != null) {
            return;
        }

        List<Set<Character>> APList = new ArrayList<>(signalSize);
        for (int i = 0; i < signalSize; i++) {
            if (i == sigIndex) {
                switch (op) {
                    case lt:
                        APList.add(constructSmallerAPs(i, comparator));
                        break;
                    case eq:
                        APList.add(constructEqAPs(i, comparator));
                        break;
                    case gt:
                        APList.add(constructLargerAPs(i, comparator));
                        break;
                    case ne:
                        Set<Character> newAPs = constructAllAPs(i);
                        newAPs.removeAll(constructEqAPs(i, comparator));
                        APList.add(newAPs);
                }
            } else {
                APList.add(constructAllAPs(i));
            }
        }

        this.satisfyingAtomicPropositions = cartesianProductCharacters(APList);
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

    @Override
    public String toOwlString() {
        constructSatisfyingAtomicPropositions();

        if (!this.satisfyingAtomicPropositions.isEmpty()) {
            return this.satisfyingAtomicPropositions.stream().map(
                            s -> String.format("(" + s + ")", getSignalName()))
                    .collect(Collectors.joining(" || "));
        } else {
            return "false";
        }
    }

    /**
     * Constructs a set of characters representing atomic propositions
     * that are smaller than the given threshold for the specified signal index.
     *
     * @param index The index of the signal.
     * @return A set of characters representing the atomic propositions.
     */
    abstract protected Set<Character> constructSmallerAPs(int index, double threshold);

    /**
     * Constructs a set of characters representing atomic propositions
     * that are greater than the given threshold for the specified signal index.
     *
     * @param index The index of the signal.
     * @return A set of characters representing the atomic propositions.
     */
    abstract protected Set<Character> constructLargerAPs(int index, double threshold);

    /**
     * Constructs a set of characters representing atomic propositions
     * that are equal to the given threshold for the specified signal index.
     *
     * @param index The index of the signal.
     * @return A set of characters representing the atomic propositions.
     */
    abstract protected Set<Character> constructEqAPs(int index, double threshold);

    /**
     * Construct the characters that represent the abstract values of the signal.
     *
     * @param index The index of the signal
     *
     */
    abstract protected Set<Character> constructAllAPs(int index);

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
     * @param maps       a list of maps to Doubles.
     * @param keyLists   a list of lists of keys. The contents of this list will be cleared.
     * @param valueLists a list of lists of values. The contents of this list will be cleared.
     * @param <T>        the type of the keys
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
