package org.group_mmm;

import net.automatalib.words.Word;

import java.util.List;
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
    public Double apply(Word<List<Double>> signal) {
        if (signal.size() <= 1) {
            return this.nullPositive ? Double.POSITIVE_INFINITY : Double.NEGATIVE_INFINITY;
        }
        return this.subFml.apply(signal.suffix(signal.size() - 1));
    }

    @Override
    public RoSI getRoSI(Word<List<Double>> signal) {
        if (signal.size() <= 1) {
            return new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY);
        }
        return this.subFml.getRoSI(signal.suffix(signal.size() - 1));
    }

    @Override
    protected void constructAtomicStrings() {
        this.atomicStrings = null;
    }

    @Override
    public String toAbstractString() {
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
