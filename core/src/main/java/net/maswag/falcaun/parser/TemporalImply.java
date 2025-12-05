package net.maswag.falcaun.parser;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

import lombok.Getter;
import net.maswag.falcaun.IOSignal;
import net.maswag.falcaun.LTLAPs;
import net.maswag.falcaun.LTLFormulaBase;

/**
 * <p>STLImply class.</p>
 *
 * @param <I> Type of the input at each step
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Getter
public class TemporalImply<I> extends AbstractTemporalLogic<I> {
    protected final TemporalLogic<I> subFml1;
    protected final TemporalLogic<I> subFml2;

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

    /**
     * {@inheritDoc}
     */
    @Override
    public Set<String> getAllAPs() {
        return subFml1.getAllAPs();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toAbstractString() {
        if (nonTemporal && iOType != IOType.BOTH) {
            return makeAbstractStringWithAtomicStrings();
        } else {
            return String.format("( %s ) -> ( %s )", subFml1.toAbstractString(), subFml2.toAbstractString());
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return String.format("( %s ) -> ( %s )", subFml1.toString(), subFml2.toString());
    }

    @Override
    public String toAbstractLTLString(Map<String, String> mapper){
        if (nonTemporal && iOType != IOType.BOTH) {
            return makeAbstractStringWithAtomicStrings(Optional.of(mapper));
        } else {
            return String.format("( %s ) -> ( %s )", subFml1.toAbstractLTLString(mapper), subFml2.toAbstractLTLString(mapper));
        }
    }

    @Override
    public String toOwlString() {
        return String.format("( %s ) -> ( %s )", subFml1.toOwlString(), subFml2.toOwlString());
    }

    @Override
    public TemporalLogic<I> toNnf(boolean negate) {
        TemporalLogic<I> simplified = new TemporalOr<>(new TemporalNot<>(subFml1), subFml2);
        return simplified.toNnf(negate);
    }

    @Override
    public TemporalLogic<I> toDisjunctiveForm() {
        TemporalLogic<I> simplified = new TemporalOr<>(new TemporalNot<>(subFml1), subFml2);
        return simplified.toDisjunctiveForm();
    }

    @Override
    public List<TemporalLogic<I>> getAllConjunctions() {
        return Arrays.asList(new TemporalNot<>(subFml1), subFml2);
    }

    public static class STLImply extends TemporalImply<List<Double>> implements STLCost {
        public STLImply(STLCost subFml1, STLCost subFml2) {
            super(subFml1, subFml2);
        }
    }

    static class LTLImply extends TemporalImply<String> implements LTLFormula {
        private final LTLFormulaBase formulaBase = new LTLFormulaBase();

        LTLImply(LTLFormula subFml1, LTLFormula subFml2) {
            super(subFml1, subFml2);
        }

        @Override
        public void setAPs(LTLAPs aps) {
            formulaBase.setAPsWithPropagation(aps, () -> {
                if (subFml1 instanceof LTLFormula) {
                    ((LTLFormula) subFml1).setAPs(aps);
                }
                if (subFml2 instanceof LTLFormula) {
                    ((LTLFormula) subFml2).setAPs(aps);
                }
            });
        }

        @Override
        public LTLAPs getAPs() {
            return formulaBase.getAps();
        }

        @Override
        public void collectAtomicPropositions(LTLAPs aps) {
            if (subFml1 instanceof LTLFormula) {
                ((LTLFormula) subFml1).collectAtomicPropositions(aps);
            }
            if (subFml2 instanceof LTLFormula) {
                ((LTLFormula) subFml2).collectAtomicPropositions(aps);
            }
        }
    }
}

