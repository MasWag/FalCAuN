package net.maswag.falcaun;

import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * <p>STLImply class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 * @param <I> Type of the input at each step
 */
public class TemporalImply<I> extends AbstractTemporalLogic<I> {
    private final TemporalLogic<I> subFml1;
    private final TemporalLogic<I> subFml2;

    TemporalImply(TemporalLogic<I> subFml1, TemporalLogic<I> subFml2) {
        this.subFml1 = subFml1;
        this.subFml2 = subFml2;
        this.nonTemporal = subFml1.isNonTemporal() && subFml2.isNonTemporal();
        this.iOType = subFml1.getIOType().merge(subFml2.getIOType());
        this.initialized = subFml1.isInitialized() && subFml2.isInitialized();
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal<I> signal) {
        return subFml1.getRoSI(signal).assignNegate().assignMax(subFml2.getRoSI(signal));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void constructSatisfyingAtomicPropositions() {
        super.constructSatisfyingAtomicPropositions();
        if (this.nonTemporal) {
            if (this.satisfyingAtomicPropositions == null) {
                this.satisfyingAtomicPropositions = new HashSet<>(getAllAPs());
                this.satisfyingAtomicPropositions.removeAll(Objects.requireNonNull(
                        subFml1.getSatisfyingAtomicPropositions()));
                this.satisfyingAtomicPropositions.addAll(Objects.requireNonNull(
                        subFml2.getSatisfyingAtomicPropositions()));
            }
        } else {
            this.satisfyingAtomicPropositions = null;
        }
    }

    /** {@inheritDoc} */
    @Override
    public Set<String> getAllAPs() {
        return subFml1.getAllAPs();
    }

    /** {@inheritDoc} */
    @Override
    public String toAbstractString() {
        if (nonTemporal && iOType != IOType.BOTH) {
            return makeAbstractStringWithAtomicStrings();
        } else {
            return String.format("( %s ) -> ( %s )", subFml1.toAbstractString(), subFml2.toAbstractString());
        }
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return String.format("( %s ) -> ( %s )", subFml1.toString(), subFml2.toString());
    }

    static class STLImply extends TemporalImply<List<Double>> implements STLCost {
        STLImply(STLCost subFml1, STLCost subFml2) {
            super(subFml1, subFml2);
        }
    }

    static class LTLImply extends TemporalImply<String> implements LTLFormula {
        LTLImply(LTLFormula subFml1, LTLFormula subFml2) {
            super(subFml1, subFml2);
        }
    }
}

