package net.maswag;

import java.util.*;
import java.util.stream.Collectors;

/**
 * <p>STLOr class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class TemporalOr<I> extends AbstractTemporalLogic<I> {
    private List<TemporalLogic<I>> subFmls;

    TemporalOr(TemporalLogic<I> subFml1, TemporalLogic<I> subFml2) {
        this.subFmls = Arrays.asList(subFml1, subFml2);
        this.nonTemporal = subFml1.isNonTemporal() && subFml2.isNonTemporal();
    }

    TemporalOr(List<TemporalLogic<I>> subFmls) {
        this.subFmls = subFmls;
        this.nonTemporal = subFmls.stream().map(TemporalLogic<I>::isNonTemporal).reduce((a, b) -> a && b).orElse(false);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal signal) {
        return subFmls.stream().map(subFml -> subFml.getRoSI(signal)).filter(
                Objects::nonNull).reduce(new RoSI(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY), RoSI::max);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return subFmls.stream().map(TemporalLogic<I>::toString).collect(Collectors.joining(" || "));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void constructAtomicStrings() {
        if (this.nonTemporal) {
            this.atomicStrings = new HashSet<>();
            for (TemporalLogic<I> subFml : subFmls) {
                this.atomicStrings.addAll(subFml.getAtomicStrings());
            }
        } else {
            this.atomicStrings = null;
        }
    }

    /** {@inheritDoc} */
    @Override
    public Set<String> getAllAPs() {
        return subFmls.get(0).getAllAPs();
    }

    /** {@inheritDoc} */
    @Override
    public String toAbstractString() {
        if (nonTemporal) {
            constructAtomicStrings();
            return this.atomicStrings.stream().map(
                    s -> "( output == \"" + s + "\" )").collect(Collectors.joining(" || "));
        } else {
            return this.subFmls.stream().map(TemporalLogic::toAbstractString).map(
                    s -> "( " + s + " )").collect(Collectors.joining(" || "));
        }
    }

    /**
     * <p>getSubFmls.</p>
     *
     * @return {@link TemporalLogic<I>} list object.
     */
    public List<TemporalLogic<I>> getSubFmls() { return this.subFmls; }

    static class STLOr extends TemporalOr<List<Double>> implements STLCost {
        STLOr(STLCost subFml1, STLCost subFml2) {
            super(subFml1, subFml2);
        }
    }

    static class LTLOr extends TemporalOr<String> implements LTLFormula {
        LTLOr(TemporalLogic<String> subFml1, TemporalLogic<String> subFml2) {
            super(subFml1, subFml2);
        }
    }
}
