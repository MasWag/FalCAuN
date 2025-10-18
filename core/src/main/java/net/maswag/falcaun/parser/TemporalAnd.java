package net.maswag.falcaun.parser;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

import lombok.Getter;
import net.maswag.falcaun.IOSignal;
import net.maswag.falcaun.LTLAPs;
import net.maswag.falcaun.LTLFormulaBase;

import java.util.stream.Collectors;

/**
 * <p>The class representing the AND operator of temporal logic.</p>
 *
 * @param <I> Type of the input at each step
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Getter
public class TemporalAnd<I> extends AbstractTemporalLogic<I> {
    private final List<TemporalLogic<I>> subFormulas;

    public TemporalAnd(TemporalLogic<I> subFml1, TemporalLogic<I> subFml2) {
        this.subFormulas = Arrays.asList(subFml1, subFml2);
        this.nonTemporal = subFml1.isNonTemporal() && subFml2.isNonTemporal();
        this.iOType = subFml1.getIOType().merge(subFml2.getIOType());
        this.initialized = subFml1.isInitialized() && subFml2.isInitialized();
    }

    public TemporalAnd(List<TemporalLogic<I>> subFormulas) {
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

    /**
     * {@inheritDoc}
     */
    @Override
    public Set<String> getAllAPs() {
        return subFormulas.get(0).getAllAPs();
    }

    @Override
    public String toOwlString() {
        return this.subFormulas.stream().map(TemporalLogic<I>::toOwlString).map(
                s -> "( " + s + " )").collect(Collectors.joining(" & "));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toAbstractString() {
        if (nonTemporal && this.iOType != IOType.BOTH) {
            return makeAbstractStringWithAtomicStrings();
        } else {
            return this.subFormulas.stream().map(TemporalLogic::toAbstractString).map(
                    s -> "( " + s + " )").collect(Collectors.joining(" && "));
        }
    }

    @Override
    public TemporalLogic<I> toNnf(boolean negate) {
        if (negate) {
            return new TemporalOr<>(subFormulas.stream().map(f -> f.toNnf(negate)).collect(Collectors.toList()));
        } else {
            return new TemporalAnd<>(subFormulas.stream().map(f -> f.toNnf(negate)).collect(Collectors.toList()));
        }
    }

    @Override
    public TemporalLogic<I> toDisjunctiveForm() {
        List<TemporalLogic<I>> convertedSubFmls = subFormulas.stream().map(f -> f.toDisjunctiveForm()).collect(Collectors.toList());
        List<TemporalLogic<I>> currentList = new ArrayList<>();
        for (TemporalLogic<I> formula : convertedSubFmls) {
            List<TemporalLogic<I>> newList = new ArrayList<>();
            if (formula instanceof TemporalOr<?>) {
                if (currentList.isEmpty()) {
                    newList.addAll(((TemporalOr<I>) formula).getSubFmls());
                } else {
                    for (TemporalLogic<I> currentFormula : currentList) {
                        for (TemporalLogic<I> subSubFormula : ((TemporalOr<I>) formula).getSubFmls()) {
                            newList.add(new TemporalAnd<>(currentFormula, subSubFormula));
                        }
                    }
                }
            } else {
                if (currentList.isEmpty()) {
                    newList.add(formula);
                } else {
                    for (TemporalLogic<I> currentFormula : currentList) {
                        newList.add(new TemporalAnd<>(formula, currentFormula));
                    }
                }
            }
            currentList = newList;
        }
        return new TemporalOr<>(currentList);
    }

    @Override
    public List<TemporalLogic<I>> getAllConjunctions() {
        List<TemporalLogic<I>> result = new ArrayList<>();
        for (TemporalLogic<I> subFml : subFormulas) {
            result.addAll(subFml.getAllConjunctions());
        }
        return result;
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
