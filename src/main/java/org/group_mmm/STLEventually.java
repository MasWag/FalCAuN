package org.group_mmm;

import net.automatalib.words.Word;

import java.util.Comparator;
import java.util.List;


public class STLEventually extends STLTemporalOp {
    STLEventually(STLCost subFml) {
        super(subFml);
    }

    @Override
    public Double apply(Word<List<Double>> signal) {
        return signal.suffixes(true).stream().map(subFml).max(Comparator.comparingDouble(Double::valueOf)).orElse(Double.NEGATIVE_INFINITY);
    }

    @Override
    public String toString() {
        return String.format("<> ( %s )", subFml.toString());
    }

    @Override
    public String toAbstractString() {
        return String.format("<> ( %s )", subFml.toAbstractString());
    }
}

