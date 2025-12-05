package net.maswag.falcaun.parser;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import lombok.Getter;
import net.maswag.falcaun.IOSignal;
import net.maswag.falcaun.LTLAPs;
import net.maswag.falcaun.LTLFormulaBase;

/**
 * <p>The class representing the OR operator of temporal logic.</p>
 *
 * @param <I> Type of the input at each step
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Getter
public class TemporalOr<I> extends AbstractTemporalLogic<I> {
    private final List<TemporalLogic<I>> subFmls;

    public TemporalOr(TemporalLogic<I> subFml1, TemporalLogic<I> subFml2) {
        this.subFmls = Arrays.asList(subFml1, subFml2);
        this.nonTemporal = subFml1.isNonTemporal() && subFml2.isNonTemporal();
        this.iOType = subFml1.getIOType().merge(subFml2.getIOType());
        this.initialized = subFml1.isInitialized() && subFml2.isInitialized();
    }

    public TemporalOr(List<TemporalLogic<I>> subFmls) {
        this.subFmls = subFmls;
        this.nonTemporal = subFmls.stream().map(TemporalLogic::isNonTemporal).reduce((a, b) -> a && b).orElse(false);
        this.iOType = subFmls.stream().map(TemporalLogic::getIOType).reduce(TemporalLogic.IOType::merge).orElse(null);
        this.initialized = subFmls.stream().map(TemporalLogic::isInitialized).reduce((a, b) -> a && b).orElse(false);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal<I> signal) {
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
    public void constructSatisfyingAtomicPropositions() {
        super.constructSatisfyingAtomicPropositions();
        if (this.nonTemporal) {
            this.satisfyingAtomicPropositions = new HashSet<>();
            for (TemporalLogic<I> subFml : subFmls) {
                this.satisfyingAtomicPropositions.addAll(
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
        return subFmls.get(0).getAllAPs();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toAbstractString() {
        if (nonTemporal && this.iOType != IOType.BOTH) {
            return makeAbstractStringWithAtomicStrings();
        } else {
            return this.subFmls.stream().map(TemporalLogic::toAbstractString).map(
                    s -> "( " + s + " )").collect(Collectors.joining(" || "));
        }
    }

    @Override
    public String toAbstractLTLString(Map<String, String> mapper){
        if (nonTemporal && this.iOType != IOType.BOTH) {
            return makeAbstractStringWithAtomicStrings(Optional.of(mapper));
        } else {
            return this.subFmls.stream().map(fml -> fml.toAbstractLTLString(mapper)).map(
                    s -> "( " + s + " )").collect(Collectors.joining(" || "));
        }
    }

    @Override
    public String toOwlString() {
        return this.subFmls.stream().map(TemporalLogic<I>::toOwlString).map(
                s -> "( " + s + " )").collect(Collectors.joining(" | "));
    }

    @Override
    public TemporalLogic<I> toNnf(boolean negate) {
        if (negate) {
            return new TemporalAnd<>(subFmls.stream().map(f -> f.toNnf(negate)).collect(Collectors.toList()));
        } else {
            return new TemporalOr<>(subFmls.stream().map(f -> f.toNnf(negate)).collect(Collectors.toList()));
        }
    }

    @Override
    public TemporalLogic<I> toDisjunctiveForm() {
        List<TemporalLogic<I>> convertedSubFmls = subFmls.stream().map(f -> f.toDisjunctiveForm()).collect(Collectors.toList());
        List<TemporalLogic<I>> newList = new ArrayList<>();
        for (TemporalLogic<I> formula : convertedSubFmls) {
            if (formula instanceof TemporalOr<?>) {
                newList.addAll(((TemporalOr<I>) formula).getSubFmls());
            } else {
                newList.add(formula);
            }
        }
        return new TemporalOr<>(newList);
    }

    @Override
    public List<TemporalLogic<I>> getAllConjunctions() {
        List<TemporalLogic<I>> result = new ArrayList<>(subFmls);
        for (TemporalLogic<I> subFml : subFmls) {
            result.addAll(subFml.getAllConjunctions());
        }
        return result;
    }

    static class STLOr extends TemporalOr<List<Double>> implements STLCost {
        STLOr(STLCost subFml1, STLCost subFml2) {
            super(subFml1, subFml2);
        }
    }

    static class LTLOr extends TemporalOr<String> implements LTLFormula {
        private final LTLFormulaBase formulaBase = new LTLFormulaBase();

        LTLOr(TemporalLogic<String> subFml1, TemporalLogic<String> subFml2) {
            super(subFml1, subFml2);
        }

        @Override
        public void setAPs(LTLAPs aps) {
            formulaBase.setAPsWithPropagation(aps, () -> {
                // Propagate to subformulas
                for (TemporalLogic<String> subFml : getSubFmls()) {
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
            for (TemporalLogic<String> subFml : getSubFmls()) {
                if (subFml instanceof LTLFormula) {
                    ((LTLFormula) subFml).collectAtomicPropositions(aps);
                }
            }
        }
    }
}
