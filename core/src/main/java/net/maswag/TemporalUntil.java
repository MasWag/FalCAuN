package net.maswag;

import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * <p>STLUntil class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class TemporalUntil<I> extends AbstractTemporalLogic<I> {
    private TemporalLogic<I> left, right;

    TemporalUntil(TemporalLogic<I> left, TemporalLogic<I> right) {
        this.left = left;
        this.right = right;
        this.nonTemporal = false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal<I> signal) {
        return getRoSIRaw(signal).assignMax(new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY));
    }

    public RoSI getRoSIRaw(IOSignal<I> signal) {
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
    public void constructAtomicStrings() {
        this.atomicStrings = null;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public Set<String> getAllAPs() {
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

    /**
     * <p>getLeft.</p>
     *
     * @return a left {@link TemporalLogic<I>} object.
     */
    public TemporalLogic<I> getLeft() { return this.left; }

    /**
     * <p>getRight.</p>
     *
     * @return a right {@link TemporalLogic<I>} object.
     */
    public TemporalLogic<I> getRight() { return this.right; }

    static class STLUntil extends TemporalUntil<List<Double>> implements STLCost {
        STLUntil(STLCost left, STLCost right) {
            super(left, right);
        }

        @Override
        public STLCost getLeft() {
            return (STLCost) super.getLeft();
        }

        @Override
        public STLCost getRight() {
            return (STLCost) super.getRight();
        }
    }

    static class LTLUntil extends TemporalUntil<String> implements LTLFormula {
        LTLUntil(TemporalLogic<String> left, TemporalLogic<String> right) {
            super(left, right);
        }
    }
}
