package net.maswag.falcaun;

import lombok.Getter;

import java.util.*;
import java.util.stream.Collectors;

/**
 * <p>The class representing the OR operator of temporal logic.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 * @param <I> Type of the input at each step
 */
@Getter
public class TemporalOr<I> extends AbstractTemporalLogic<I> {
    private final List<TemporalLogic<I>> subFmls;

    TemporalOr(TemporalLogic<I> subFml1, TemporalLogic<I> subFml2) {
        this.subFmls = Arrays.asList(subFml1, subFml2);
        this.nonTemporal = subFml1.isNonTemporal() && subFml2.isNonTemporal();
        this.iOType = subFml1.getIOType().merge(subFml2.getIOType());
        this.initialized = subFml1.isInitialized() && subFml2.isInitialized();
    }

    TemporalOr(List<TemporalLogic<I>> subFmls) {
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

    /** {@inheritDoc} */
    @Override
    public Set<String> getAllAPs() {
        return subFmls.get(0).getAllAPs();
    }

    /** {@inheritDoc} */
    @Override
    public String toAbstractString() {
        if (nonTemporal && this.iOType != IOType.BOTH) {
            return makeAbstractStringWithAtomicStrings();
        } else {
            return this.subFmls.stream().map(TemporalLogic::toAbstractString).map(
                    s -> "( " + s + " )").collect(Collectors.joining(" || "));
        }
    }

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
