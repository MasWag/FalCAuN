package org.group_mmm;

import java.util.Set;

/**
 * <p>STLNext class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class STLNext extends STLCost {
    private STLCost subFml;
    private boolean nullPositive;

    STLNext(STLCost subFml, boolean nullPositive) {
        this.subFml = subFml;
        this.nullPositive = nullPositive;
        this.nonTemporal = false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Double apply(IOSignal signal) {
        if (signal.size() <= 1) {
            return this.nullPositive ? Double.POSITIVE_INFINITY : Double.NEGATIVE_INFINITY;
        }
        return this.subFml.apply(signal.suffix(signal.size() - 1));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal signal) {
        if (signal.size() <= 1) {
            return new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY);
        }
        return this.subFml.getRoSI(signal.suffix(signal.size() - 1));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void constructAtomicStrings() {
        this.atomicStrings = null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toAbstractString() {
        return String.format("X ( %s )", subFml.toAbstractString());
    }

    /** {@inheritDoc} */
    @Override
    protected Set<String> getAllAPs() {
        return subFml.getAllAPs();
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return String.format("X ( %s )", subFml.toString());
    }

    /**
     * <p>getSubFml.</p>
     *
     * @return a {@link STLCost} object.
     */
    public STLCost getSubFml() { return this.subFml; }
}
