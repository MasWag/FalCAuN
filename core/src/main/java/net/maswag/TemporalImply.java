package net.maswag;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * <p>STLImply class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class TemporalImply<I> extends AbstractTemporalLogic<I> {
    private final TemporalLogic<I> subFml1;
    private final TemporalLogic<I> subFml2;

    TemporalImply(TemporalLogic<I> subFml1, TemporalLogic<I> subFml2) {
        this.subFml1 = subFml1;
        this.subFml2 = subFml2;
        this.nonTemporal = subFml1.isNonTemporal() && subFml2.isNonTemporal();
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
    public void constructAtomicStrings() {
        if (this.nonTemporal) {
            if (this.atomicStrings == null) {
                this.atomicStrings = new HashSet<>(getAllAPs());
                this.atomicStrings.removeAll(subFml1.getAtomicStrings());
                this.atomicStrings.addAll(subFml2.getAtomicStrings());
            }
        } else {
            this.atomicStrings = null;
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
        if (nonTemporal) {
            constructAtomicStrings();
            return this.atomicStrings.stream().map(
                    s -> "( output == \"" + s + "\" )").collect(Collectors.joining(" || "));
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

