package net.maswag;

import java.util.Objects;
import java.util.Set;

/**
 * <p>STLRelease class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class STLRelease extends STLCost {
    private final STLCost left, right;

    STLRelease(STLCost left, STLCost right) {
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
                    right.length() - left.length()).limit(i + 1).map(this.left::getRoSI).filter(Objects::nonNull).reduce(nextRoSI, RoSI::max);
            result.assignMin(globalRoSI);
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return this.left + " R " + this.right;
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
        return "( " + this.left.toAbstractString() + " ) R ( " + this.right.toAbstractString() + " )";
    }

    /**
     * <p>getLeft.</p>
     *
     * @return a left {@link STLCost} object.
     */
    public STLCost getLeft() {
        return this.left;
    }

    /**
     * <p>getRight.</p>
     *
     * @return a right {@link STLCost} object.
     */
    public STLCost getRight() {
        return this.right;
    }
}
