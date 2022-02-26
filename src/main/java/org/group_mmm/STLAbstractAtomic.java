package org.group_mmm;

import net.automatalib.words.Word;

import java.util.*;
import java.util.stream.Collectors;

import static java.lang.Math.abs;

/**
 * <p>STLAtomic class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
abstract public class STLAbstractAtomic extends STLCost {
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

            this.allAPs = constructProductAPs(APList);
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
        if (this.atomicStrings != null) {
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

        this.atomicStrings = constructProductAPs(APList);
    }

    @Override
    public Set<String> getAtomicStrings() {
        if (atomicStrings == null) {
            constructAtomicStrings();
        }
        return atomicStrings;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toAbstractString() {
        constructAtomicStrings();

        return this.atomicStrings.stream().map(
                s -> String.format("( %s == \"" + s + "\" )", getSignalName()))
                .collect(Collectors.joining(" || "));
    }

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

    private Set<Character> constructLargerAPs(List<List<Double>> concreteValues,
                                              List<List<Character>> abstractValues,
                                              List<Character> largest, int index, double threshold) {
        int bsResult = Collections.binarySearch(concreteValues.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? bsResult : (~bsResult - 1);
        Set<Character> resultAPs = new HashSet<>(abstractValues.get(index).subList(thresholdIndex + 1, abstractValues.get(index).size()));

        resultAPs.add(largest.get(index));


        return resultAPs;
    }

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

    Set<Character> constructAllAPs(List<List<Character>> abstractValues, List<Character> largest, int index) {
        Set<Character> resultAPs = new HashSet<>(abstractValues.get(index));
        resultAPs.add(largest.get(index));
        return resultAPs;
    }

    protected Set<String> constructProductAPs(List<Set<Character>> APList) {
        Set<String> APs = null;
        for (Set<Character> currentAPs : APList) {
            Set<String> newAPs = new HashSet<>();
            if (APs != null) {
                for (String previousAP : APs) {
                    for (Character currentAP : currentAPs) {
                        newAPs.add(previousAP + currentAP);
                    }
                }
            } else {
                newAPs.addAll(currentAPs.stream().map(String::valueOf).collect(Collectors.toList()));
            }
            APs = newAPs;
        }
        return APs;
    }

    public enum Operation {
        lt,
        eq,
        gt,
        ne
    }
}
