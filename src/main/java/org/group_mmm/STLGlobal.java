package org.group_mmm;

import net.automatalib.words.Word;

import java.util.List;
import java.util.Objects;

/**
 * <p>STLGlobal class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class STLGlobal extends STLTemporalOp {
    STLGlobal(STLCost subFml) {
        super(subFml);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(Word<List<Double>> signal) {
        return getRoSIRaw(signal).assignMin(new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY));
    }

    /**
     * {@inheritDoc}
     */
    public RoSI getRoSIRaw(Word<List<Double>> signal) {
        return signal.suffixes(true).stream().filter(w -> !w.isEmpty()).map(w -> subFml.getRoSI(w)).filter(Objects::nonNull)
                .reduce(new RoSI(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY), RoSI::min);
    }

    /**
     * {@inheritDoc}
     */
    public RoSI getRoSIRawWithLen(Word<List<Double>> signal, int length) {
        return signal.suffixes(true).subList(0, length).stream().filter(w -> !w.isEmpty()).map(w -> subFml.getRoSI(w)).filter(Objects::nonNull)
                .reduce(new RoSI(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY), RoSI::min);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toAbstractString() {
        return String.format("[] ( %s )", subFml.toAbstractString());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return String.format("[] ( %s )", subFml.toString());
    }
}
