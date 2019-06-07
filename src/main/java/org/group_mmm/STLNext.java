package org.group_mmm;

import net.automatalib.words.Word;

import java.util.ArrayList;

public class STLNext extends STLCost {
    private STLCost subFml;

    public STLNext(STLCost subFml) {
        this.subFml = subFml;
    }

    @Override
    public Double apply(Word<ArrayList<Double>> signal) {
        return this.subFml.apply(signal.suffix(signal.size() - 1));
    }
}
