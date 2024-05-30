package net.maswag.falcaun;

import lombok.Getter;

import java.util.List;
import java.util.Set;

/**
 * <p>STLNext class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 * @param <I> Type of the input at each step
 */
public class TemporalNext<I> extends AbstractTemporalLogic<I> {
    @Getter
    private TemporalLogic<I> subFml;
    private final boolean nullPositive;

    TemporalNext(TemporalLogic<I> subFml, boolean nullPositive) {
        this.subFml = subFml;
        this.nullPositive = nullPositive;
        this.nonTemporal = false;
        this.iOType = subFml.getIOType();
        this.initialized = subFml.isInitialized();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Double apply(IOSignal<I> signal) {
        if (signal.size() <= 1) {
            return this.nullPositive ? Double.POSITIVE_INFINITY : Double.NEGATIVE_INFINITY;
        }
        return this.subFml.apply(signal.suffix(signal.size() - 1));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal<I> signal) {
        if (signal.size() <= 1) {
            return new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY);
        }
        return this.subFml.getRoSI(signal.suffix(signal.size() - 1));
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
    public String toAbstractString() {
        return String.format("X ( %s )", subFml.toAbstractString());
    }

    /** {@inheritDoc} */
    @Override
    public Set<String> getAllAPs() {
        return subFml.getAllAPs();
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return String.format("X ( %s )", subFml.toString());
    }

    static class STLNext extends TemporalNext<List<Double>> implements STLCost {
        STLNext(STLCost subFml, boolean nullPositive) {
            super(subFml, nullPositive);
        }
    }

    static class LTLNext extends TemporalNext<String> implements LTLFormula {
        LTLNext(LTLFormula subFml, boolean nullPositive) {
            super(subFml, nullPositive);
        }
    }
}
