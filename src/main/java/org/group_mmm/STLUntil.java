package org.group_mmm;

import java.util.Objects;
import java.util.Set;

/**
 * <p>STLUntil class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class STLUntil extends STLCost {
    private STLCost left, right;

    STLUntil(STLCost left, STLCost right) {
        this.left = left;
        this.right = right;
        this.nonTemporal = false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal signal) {
        return getRoSIRaw(signal).assignMax(new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY));
    }

    public RoSI getRoSIRaw(IOSignal signal) {
        RoSI result = new RoSI(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY);

        for (int i = 0; i < signal.length(); i++) {
            RoSI nextRoSI = this.right.getRoSI(signal.subWord(i));
            RoSI globalRoSI = signal.prefixes(true).stream().sorted((left, right) ->
                    right.length() - left.length()).limit(i + 1).map(suffix ->
                    this.left.getRoSI(suffix)).filter(Objects::nonNull).reduce(nextRoSI, RoSI::min);
            result.assignMax(globalRoSI);
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return this.left + " U " + this.right;
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
    protected Set<String> getAllAPs() {
        Set<String> allAPs = this.left.getAllAPs();
        allAPs.addAll(this.right.getAllAPs());
        return allAPs;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toAbstractString() {
        return "( " + this.left.toAbstractString() + " ) U ( " + this.right.toAbstractString() + " )";
    }
}
