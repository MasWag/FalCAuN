package net.maswag.falcaun;

import lombok.Getter;

import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * <p>STLRelease class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 * @param <I> Type of the input at each step
 */
@Getter
public class TemporalRelease<I> extends AbstractTemporalLogic<I> {
    private final TemporalLogic<I> left, right;

    TemporalRelease(TemporalLogic<I> left, TemporalLogic<I> right) {
        this.left = left;
        this.right = right;
        this.nonTemporal = false;
        this.iOType = left.getIOType().merge(right.getIOType());
        this.initialized = left.isInitialized() && right.isInitialized();
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
    public void constructSatisfyingAtomicPropositions() {
        this.satisfyingAtomicPropositions = null;
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
        return "( " + this.left.toAbstractString() + " ) R ( " + this.right.toAbstractString() + " )";
    }

    static class STLRelease extends TemporalRelease<List<Double>> implements STLCost {
        STLRelease(STLCost left, STLCost right) {
            super(left, right);
        }
    }

    static class LTLRelease extends TemporalRelease<String> implements LTLFormula {
        LTLRelease(LTLFormula left, LTLFormula right) {
            super(left, right);
        }
    }
}
