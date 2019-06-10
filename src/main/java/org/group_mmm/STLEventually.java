package org.group_mmm;

import net.automatalib.words.Word;

import java.util.ArrayList;
import java.util.Comparator;


public class STLEventually extends STLTemporalOp {
    STLEventually(STLCost subFml) {
        super(subFml);
    }

    @Override
    public Double apply(Word<ArrayList<Double>> signal) {
        return signal.suffixes(true).stream().map(subFml).max(Comparator.comparingDouble(Double::valueOf)).orElse(null);
    }

    @Override
    public String toString() {
        return String.format("<> ( %s )", subFml.toString());
    }

    @Override
    String toAbstractString() {
        return String.format("<> ( %s )", subFml.toAbstractString());
    }
}

