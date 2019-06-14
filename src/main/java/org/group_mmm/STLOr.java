package org.group_mmm;

import net.automatalib.words.Word;

import java.util.*;
import java.util.stream.Collectors;

public class STLOr extends STLCost {
    private STLCost subFml1, subFml2;
    private List<STLCost> subFmls;

    STLOr(STLCost subFml1, STLCost subFml2) {
        this.subFmls = Arrays.asList(subFml1, subFml2);
        this.nonTemporal = subFml1.nonTemporal && subFml2.nonTemporal;
    }

    STLOr(List<STLCost> subFmls) {
        this.subFmls = subFmls;
        this.nonTemporal = subFmls.stream().map(STLCost::isNonTemporal).reduce((a, b) -> a && b).orElse(false);
    }

    @Override
    public Double apply(Word<ArrayList<Double>> signal) {
        return subFmls.stream().map(subFml -> subFml.apply(signal)).filter(Objects::nonNull).max(Comparator.comparingDouble(Double::valueOf)).orElse(Double.NEGATIVE_INFINITY);
    }

    @Override
    public String toString() {
        return subFmls.stream().map(STLCost::toString).collect(Collectors.joining(" || "));
    }

    @Override
    protected void constructAtomicStrings() {
        if (this.nonTemporal) {
            this.atomicStrings = new HashSet<>();
            for (STLCost subFml : subFmls) {
                this.atomicStrings.add(subFml.toAbstractString());
            }
        } else {
            this.atomicStrings = null;
        }
    }

    @Override
    protected Set<String> getAllAPs() {
        return subFmls.get(0).getAllAPs();
    }

    @Override
    String toAbstractString() {
        if (nonTemporal) {
            constructAtomicStrings();
            return this.atomicStrings.stream().map(
                    s -> "( output == \"" + s + "\" )").collect(Collectors.joining(" || "));
        } else {
            return this.subFmls.stream().map(STLCost::toAbstractString).map(
                    s -> "( " + s + " )").collect(Collectors.joining(" || "));
        }
    }
}
