package org.group_mmm;

import net.automatalib.words.Word;

import java.util.Comparator;
import java.util.List;
import java.util.Objects;

public class STLGlobal extends STLTemporalOp {
    STLGlobal(STLCost subFml) {
        super(subFml);
    }

    @Override
    public Double apply(Word<List<Double>> signal) {
        return signal.suffixes(true).stream().map(subFml).filter(Objects::nonNull).min(Comparator.comparingDouble(Double::valueOf)).orElse(Double.POSITIVE_INFINITY);
    }

    @Override
    public String toAbstractString() {
        return String.format("[] ( %s )", subFml.toAbstractString());
    }

    @Override
    public String toString() {
        return String.format("[] ( %s )", subFml.toString());
    }
}
