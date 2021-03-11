package org.group_mmm;

import java.util.Objects;


/**
 * <p>STLEventually class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class STLEventually extends STLTemporalOp {
    STLEventually(STLCost subFml) {
        super(subFml);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal signal) {
        return getRoSIRaw(signal).assignMax(new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY));
    }

    /**
     * {@inheritDoc}
     */
    public RoSI getRoSIRaw(IOSignal signal) {
        return signal.suffixes(true).stream().map(w -> subFml.getRoSI(w)).filter(Objects::nonNull)
                .reduce(new RoSI(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY), RoSI::max);
    }

    /**
     * {@inheritDoc}
     */
    public RoSI getRoSIRawWithLen(IOSignal signal, int length) {
        return signal.suffixes(true).subList(0, length).stream().map(w -> subFml.getRoSI(w)).filter(Objects::nonNull)
                .reduce(new RoSI(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY), RoSI::max);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return String.format("<> ( %s )", subFml.toString());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toAbstractString() {
        return String.format("<> ( %s )", subFml.toAbstractString());
    }
}

