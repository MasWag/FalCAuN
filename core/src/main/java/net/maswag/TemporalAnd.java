package net.maswag;

import lombok.Getter;

import java.util.*;
import java.util.stream.Collectors;

@Getter
class TemporalAnd<I> extends AbstractTemporalLogic<I> {
    private final List<TemporalLogic<I>> subFormulas;

    TemporalAnd(TemporalLogic<I> subFml1, TemporalLogic<I> subFml2) {
        this.subFormulas = Arrays.asList(subFml1, subFml2);
        this.nonTemporal = subFml1.isNonTemporal() && subFml2.isNonTemporal();
    }

    TemporalAnd(List<TemporalLogic<I>> subFormulas) {
        this.subFormulas = subFormulas;
        this.nonTemporal = subFormulas.stream().map(TemporalLogic::isNonTemporal).reduce((a, b) -> a && b).orElse(false);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal<I> signal) {
        return subFormulas.stream().map(subFml -> subFml.getRoSI(signal)).filter(
                Objects::nonNull).reduce(new RoSI(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY), RoSI::min);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return subFormulas.stream().map(TemporalLogic<I>::toString).collect(Collectors.joining(" && "));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void constructAtomicStrings() {
        if (this.nonTemporal) {
            this.atomicStrings = new HashSet<>(getAllAPs());
            for (TemporalLogic<I> subFml : subFormulas) {
                this.atomicStrings.retainAll(subFml.getAtomicStrings());
            }
        } else {
            this.atomicStrings = null;
        }
    }

    /** {@inheritDoc} */
    @Override
    public Set<String> getAllAPs() {
        return subFormulas.get(0).getAllAPs();
    }

    /** {@inheritDoc} */
    @Override
    public String toAbstractString() {
        if (nonTemporal) {
            constructAtomicStrings();
            return this.atomicStrings.stream().map(
                    s -> "( output == \"" + s + "\" )").collect(Collectors.joining(" || "));
        } else {
            return this.subFormulas.stream().map(TemporalLogic<I>::toAbstractString).map(
                    s -> "( " + s + " )").collect(Collectors.joining(" && "));
        }
    }

    static class STLAnd extends TemporalAnd<List<Double>> implements STLCost {
        STLAnd(STLCost subFml1, STLCost subFml2) {
            super(subFml1, subFml2);
        }

        STLAnd(List<TemporalLogic<List<Double>>> subFormulas) {
            super(subFormulas);
        }
    }

    static class LTLAnd extends TemporalAnd<String> implements LTLFormula {
        LTLAnd(LTLFormula subFml1, LTLFormula subFml2) {
            super(subFml1, subFml2);
        }

        LTLAnd(List<TemporalLogic<String>> subFormulas) {
            super(subFormulas);
        }
    }
}
