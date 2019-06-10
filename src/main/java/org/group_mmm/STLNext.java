package org.group_mmm;

import net.automatalib.words.Word;

import java.util.ArrayList;
import java.util.Set;

public class STLNext extends STLCost {
    private STLCost subFml;
    private boolean nullPositive;

    STLNext(STLCost subFml, boolean nullPositive) {
        this.subFml = subFml;
        this.nullPositive = nullPositive;
        this.nonTemporal = false;
    }

    @Override
    public Double apply(Word<ArrayList<Double>> signal) {
        if (signal.size() <= 1) {
            return this.nullPositive ? Double.POSITIVE_INFINITY : Double.NEGATIVE_INFINITY;
        }
        return this.subFml.apply(signal.suffix(signal.size() - 1));
    }

    @Override
    protected void constructAtomicStrings() {
        this.atomicStrings = null;
    }

    @Override
    String toAbstractString() {
        return String.format("X ( %s )", subFml.toAbstractString());
    }

    @Override
    protected Set<String> getAllAPs() {
        return subFml.getAllAPs();
    }

    @Override
    public String toString() {
        return String.format("X ( %s )", subFml.toString());
    }
}
