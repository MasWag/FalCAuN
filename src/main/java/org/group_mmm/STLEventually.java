package org.group_mmm;

import net.automatalib.words.Word;

import java.util.List;
import java.util.Objects;


public class STLEventually extends STLTemporalOp {
    STLEventually(STLCost subFml) {
        super(subFml);
    }

    @Override
    public RoSI getRoSI(Word<List<Double>> signal) {
        return getRoSIRaw(signal).assignMax(new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY));
    }

    public RoSI getRoSIRaw(Word<List<Double>> signal) {
        return signal.suffixes(true).stream().map(w -> subFml.getRoSI(w)).filter(Objects::nonNull)
                .reduce(new RoSI(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY), RoSI::max);
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

