package net.maswag.falcaun;

import lombok.Getter;

import java.util.*;
import java.util.stream.Collectors;

/**
 * <p>The class representing the AND operator of temporal logic.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 * @param <I> Type of the input at each step
 */
@Getter
class TemporalAnd<I> extends AbstractTemporalLogic<I> {
    private final List<TemporalLogic<I>> subFormulas;

    TemporalAnd(TemporalLogic<I> subFml1, TemporalLogic<I> subFml2) {
        this.subFormulas = Arrays.asList(subFml1, subFml2);
        this.nonTemporal = subFml1.isNonTemporal() && subFml2.isNonTemporal();
        this.iOType = subFml1.getIOType().merge(subFml2.getIOType());
        this.initialized = subFml1.isInitialized() && subFml2.isInitialized();
    }

    TemporalAnd(List<TemporalLogic<I>> subFormulas) {
        this.subFormulas = subFormulas;
        this.nonTemporal = subFormulas.stream().map(TemporalLogic::isNonTemporal).reduce((a, b) -> a && b).orElse(false);
        this.iOType = subFormulas.stream().map(TemporalLogic::getIOType).reduce(TemporalLogic.IOType::merge).orElse(null);
        this.initialized = subFormulas.stream().map(TemporalLogic::isInitialized).reduce((a, b) -> a && b).orElse(false);
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
    public void constructSatisfyingAtomicPropositions() {
        super.constructSatisfyingAtomicPropositions();
        if (this.nonTemporal) {
            this.satisfyingAtomicPropositions = new HashSet<>(getAllAPs());
            for (TemporalLogic<I> subFml : subFormulas) {
                this.satisfyingAtomicPropositions.retainAll(
                        Objects.requireNonNull(subFml.getSatisfyingAtomicPropositions()));
            }
        } else {
            this.satisfyingAtomicPropositions = null;
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
        if (nonTemporal && this.iOType != IOType.BOTH) {
            return makeAbstractStringWithAtomicStrings();
        } else {
            return this.subFormulas.stream().map(TemporalLogic::toAbstractString).map(
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
        private final LTLFormulaBase formulaBase = new LTLFormulaBase();
        
        LTLAnd(LTLFormula subFml1, LTLFormula subFml2) {
            super(subFml1, subFml2);
        }

        LTLAnd(List<TemporalLogic<String>> subFormulas) {
            super(subFormulas);
        }
        
        @Override
        public void setAPs(LTLAPs aps) {
            formulaBase.setAPsWithPropagation(aps, () -> {
                // Propagate to subformulas
                for (TemporalLogic<String> subFml : getSubFormulas()) {
                    if (subFml instanceof LTLFormula) {
                        ((LTLFormula) subFml).setAPs(aps);
                    }
                }
            });
        }
        
        @Override
        public LTLAPs getAPs() {
            return formulaBase.getAps();
        }
        
        @Override
        public void collectAtomicPropositions(LTLAPs aps) {
            for (TemporalLogic<String> subFml : getSubFormulas()) {
                if (subFml instanceof LTLFormula) {
                    ((LTLFormula) subFml).collectAtomicPropositions(aps);
                }
            }
        }
    }
}
