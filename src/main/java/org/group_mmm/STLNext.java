package org.group_mmm;

import net.automatalib.words.Word;

import java.util.ArrayList;

public class STLNext extends STLCost {
    private STLCost subFml;
    private boolean nullPositive;

    STLNext(STLCost subFml, boolean nullPositive) {
        this.subFml = subFml;
        this.nullPositive = nullPositive;
    }

    @Override
    public Double apply(Word<ArrayList<Double>> signal) {
        if (signal.size() <= 1) {
            return this.nullPositive ? Double.POSITIVE_INFINITY : Double.NEGATIVE_INFINITY;
        }
        return this.subFml.apply(signal.suffix(signal.size() - 1));
    }
}
