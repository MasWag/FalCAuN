package org.group_mmm;

import net.automatalib.words.Word;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.Objects;

public class STLGlobal extends STLCost {
    private STLCost subFml;

    STLGlobal(STLCost subFml) {
        this.subFml = subFml;
    }

    @Override
    public Double apply(Word<ArrayList<Double>> signal) {
        return signal.suffixes(true).stream().map(subFml).filter(Objects::nonNull).min(Comparator.comparingDouble(Double::valueOf)).orElse(Double.POSITIVE_INFINITY);
    }
}
