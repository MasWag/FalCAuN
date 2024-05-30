package net.maswag.falcaun;

import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * <p>STLTemporalNot class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 * @param <I> Type of the input at each step
 */
public class TemporalNot<I> extends AbstractTemporalLogic<I> {
    private final TemporalLogic<I> subFml;

    TemporalNot(TemporalLogic<I> subFml) {
        this.subFml = subFml;
        this.nonTemporal = subFml.isNonTemporal();
        this.iOType = subFml.getIOType();
        this.initialized = subFml.isInitialized();
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal<I> signal) {
        return subFml.getRoSI(signal).assignNegate();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void constructSatisfyingAtomicPropositions() {
        if (this.nonTemporal) {
            if (this.satisfyingAtomicPropositions == null) {
                this.satisfyingAtomicPropositions = new HashSet<>(getAllAPs());
                this.satisfyingAtomicPropositions.removeAll(
                        Objects.requireNonNull(subFml.getSatisfyingAtomicPropositions()));
            }
        } else {
            this.satisfyingAtomicPropositions = null;
        }
    }

    /** {@inheritDoc} */
    @Override
    public Set<String> getAllAPs() {
        return subFml.getAllAPs();
    }

    /** {@inheritDoc} */
    @Override
    public String toAbstractString() {
        return String.format("!( %s )", subFml.toAbstractString());
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return String.format("!( %s )", subFml.toString());
    }

    static class STLNot extends TemporalNot<List<Double>> implements STLCost {
        STLNot(STLCost subFml) {
            super(subFml);}
    }

    static class LTLNot extends TemporalNot<String> implements LTLFormula {
        LTLNot(LTLFormula subFml) {
            super(subFml);
        }
    }
}

