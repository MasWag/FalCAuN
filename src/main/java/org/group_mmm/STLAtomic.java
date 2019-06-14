package org.group_mmm;

import net.automatalib.words.Word;

import java.util.*;
import java.util.stream.Collectors;

import static java.lang.Math.abs;

public class STLAtomic extends STLCost {
    private final int gearIndex = 2;
    private Operation op;
    private int sigIndex;
    private double comparator;
    private ArrayList<ArrayList<Character>> abstractOutputs = new ArrayList<>();
    private ArrayList<ArrayList<Double>> concreteOutputs = new ArrayList<>();
    private List<Character> largest = new ArrayList<>();
    private Set<String> allAPs;
    private List<Map<Character, Double>> outputMapper;

    STLAtomic(int sigIndex, Operation op, double comparator) {
        this.sigIndex = sigIndex;
        this.comparator = comparator;
        this.op = op;
        this.nonTemporal = true;
    }

    @Override
    public Set<String> getAllAPs() {
        if (this.allAPs == null) {
            List<Set<Character>> APList = new ArrayList<>(abstractOutputs.size());
            for (int i = 0; i < abstractOutputs.size(); i++) {
                APList.add(constructAllAPs(i));
            }

            this.allAPs = constructProductAPs(APList);
        }
        return allAPs;
    }

    private void setOutputMaps() {
        abstractOutputs.clear();
        concreteOutputs.clear();
        for (Map<Character, Double> entry : outputMapper) {
            ArrayList<Character> cList = new ArrayList<>(entry.keySet());
            ArrayList<Double> dList = new ArrayList<>(entry.values());
            assert cList.size() == dList.size();
            abstractOutputs.add(cList);
            concreteOutputs.add(dList);
        }
    }

    void setOutputMapper(List<Map<Character, Double>> outputMapper) {
        this.outputMapper = outputMapper;
        setOutputMaps();
    }

    void setLargest(List<Character> largest) {
        this.largest = largest;
        setOutputMaps();
    }

    @Override
    public Double apply(Word<ArrayList<Double>> signal) {
        ArrayList<Double> currentValue;

        if (signal.isEmpty()) {
            return Double.POSITIVE_INFINITY;
        }
        currentValue = signal.getSymbol(0);
        if (currentValue == null) {
            return Double.POSITIVE_INFINITY;
        }
        switch (op) {
            case lt:
                return comparator - currentValue.get(sigIndex);
            case gt:
                return currentValue.get(sigIndex) - comparator;
            case eq:
                return -abs(currentValue.get(sigIndex) - comparator);
            default:
                return null;
        }
    }

    @Override
    public String toString() {
        switch (op) {
            case lt:
                return String.format("signal(%d) < %f", sigIndex, comparator);
            case eq:
                return String.format("signal(%d) == %f", sigIndex, comparator);
            case gt:
                return String.format("signal(%d) > %f", sigIndex, comparator);
        }
        return null;
    }

    @Override
    protected void constructAtomicStrings() {
        if (this.atomicStrings != null) {
            return;
        }

        List<Set<Character>> APList = new ArrayList<>(abstractOutputs.size());
        for (int i = 0; i < abstractOutputs.size(); i++) {
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
                }
            } else {
                APList.add(constructAllAPs(i));
            }
        }

        this.atomicStrings = constructProductAPs(APList);
    }

    @Override
    Set<String> getAtomicStrings() {
        if (atomicStrings == null) {
            constructAtomicStrings();
        }
        return atomicStrings;
    }

    @Override
    String toAbstractString() {
        constructAtomicStrings();

        return this.atomicStrings.stream().map(
                s -> "( output == \"" + s + "\" )").collect(Collectors.joining(" || "));
    }

    private Set<Character> constructSmallerAPs(int index, double threshold) {
        int bsResult = Collections.binarySearch(concreteOutputs.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? bsResult : (~bsResult - 1);
        Set<Character> resultAPs = new HashSet<>(abstractOutputs.get(index).subList(0, thresholdIndex + 1));
        if (bsResult < 0 && thresholdIndex == abstractOutputs.size() - 1) {
            resultAPs.add(largest.get(index));
        }

        return resultAPs;
    }

    private Set<Character> constructLargerAPs(int index, double threshold) {
        int bsResult = Collections.binarySearch(concreteOutputs.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? bsResult : (~bsResult - 1);
        Set<Character> resultAPs = new HashSet<>(abstractOutputs.get(index).subList(thresholdIndex + 1, abstractOutputs.get(index).size()));

        resultAPs.add(largest.get(index));


        return resultAPs;
    }

    private Set<Character> constructEqAPs(int index, double threshold) {
        int bsResult = Collections.binarySearch(concreteOutputs.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? bsResult : (~bsResult);
        Set<Character> resultAPs = new HashSet<>();
        if (!abstractOutputs.get(index).isEmpty()) {
            resultAPs.addAll(abstractOutputs.get(index).subList(thresholdIndex, thresholdIndex + 1));
        }
        if (abstractOutputs.get(index).isEmpty() ||
                (bsResult < 0 && thresholdIndex == abstractOutputs.size() - 1)) {
            resultAPs.add(largest.get(index));
        }
        assert resultAPs.size() == 1;

        return resultAPs;
    }

    private Set<Character> constructAllAPs(int index) {
        Set<Character> resultAPs = new HashSet<>(abstractOutputs.get(index));
        resultAPs.add(largest.get(index));
        return resultAPs;
    }

    private Set<String> constructProductAPs(List<Set<Character>> APList) {
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

    enum Operation {
        lt,
        eq,
        gt
    }
}
