package net.maswag.falcaun.parser;

import java.util.Objects;

import net.maswag.falcaun.IOSignal;
import net.maswag.falcaun.LTLAPs;
import net.maswag.falcaun.LTLFormulaBase;


import java.util.List;


/**
 * <p>STLEventually class.</p>
 *
 * @param <I> Type of the input at each step
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class TemporalEventually<I> extends TemporalOp<I> {
    public TemporalEventually(TemporalLogic<I> subFml) {
        super(subFml);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal<I> signal) {
        return getRoSIRaw(signal).assignMax(new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY));
    }

    /**
     * {@inheritDoc}
     */
    public RoSI getRoSIRaw(IOSignal<I> signal) {
        return signal.suffixes(true).stream().map(w -> subFml.getRoSI(w)).filter(Objects::nonNull)
                .reduce(new RoSI(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY), RoSI::max);
    }

    /**
     * {@inheritDoc}
     */
    public RoSI getRoSIRawWithLen(IOSignal<I> signal, int length) {
        return signal.suffixes(true).subList(0, length).stream().map(w -> subFml.getRoSI(w)).filter(Objects::nonNull)
                .reduce(new RoSI(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY), RoSI::max);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return String.format("<> ( %s )", subFml.toString());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toAbstractString() {
        return String.format("<> ( %s )", subFml.toAbstractString());
    }

    @Override
    public String toOwlString() {
        return String.format("F ( %s )", subFml.toOwlString());
    }

    /**
     * <p>getSubFml.</p>
     *
     * @return a {@link TemporalLogic<I>} object.
     */
    public TemporalLogic<I> getSubFml() {
        return this.subFml;
    }

    @Override
    public TemporalLogic<I> toNnf(boolean negate) {
        if (negate) {
            return new TemporalGlobally<>(subFml.toNnf(negate));
        } else {
            return new TemporalEventually<>(subFml.toNnf(negate));
        }
    }

    @Override
    public TemporalLogic<I> toDisjunctiveForm() {
        return new TemporalEventually<>(subFml.toDisjunctiveForm());
    }

    @Override
    public List<TemporalLogic<I>> getAllConjunctions() {
        return subFml.getAllConjunctions();
    }

    static class STLEventually extends TemporalEventually<List<Double>> implements STLCost {
        STLEventually(STLCost subFml) {
            super(subFml);
        }

        @Override
        public STLCost getSubFml() {
            return (STLCost) this.subFml;
        }
    }

    static class LTLEventually extends TemporalEventually<String> implements LTLFormula {
        private final LTLFormulaBase formulaBase = new LTLFormulaBase();

        LTLEventually(LTLFormula subFml) {
            super(subFml);
        }

        @Override
        public void setAPs(LTLAPs aps) {
            formulaBase.setAPsWithPropagation(aps, () -> {
                if (getSubFml() instanceof LTLFormula) {
                    ((LTLFormula) getSubFml()).setAPs(aps);
                }
            });
        }

        @Override
        public LTLAPs getAPs() {
            return formulaBase.getAps();
        }

        @Override
        public void collectAtomicPropositions(LTLAPs aps) {
            if (subFml instanceof LTLFormula) {
                ((LTLFormula) subFml).collectAtomicPropositions(aps);
            }
        }
    }
}

