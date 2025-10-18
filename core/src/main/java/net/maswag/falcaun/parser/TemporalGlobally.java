package net.maswag.falcaun.parser;

import lombok.Getter;

import java.util.List;

import net.maswag.falcaun.IOSignal;
import net.maswag.falcaun.LTLAPs;
import net.maswag.falcaun.LTLFormulaBase;

/**
 * <p>TemporalGlobally class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 * @param <I> Type of the input at each step
 */
@Getter
public class TemporalGlobally<I> extends TemporalOp<I> {
    public TemporalGlobally(TemporalLogic<I> subFml) {
        super(subFml);
    }
    
    /**
     * Get the sub-formula
     * @return the sub-formula
     */
    public TemporalLogic<I> getSubFml() {
        return subFml;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal<I> signal) {
        return getRoSIRaw(signal).assignMin(new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSIRaw(IOSignal<I> signal) {
        RoSI result = new RoSI(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY);
        for (int i = 0; i < signal.length(); i++) {
            // suffix(n) returns the last n elements, so for position i we need suffix(length - i)
            IOSignal<I> suffix = signal.suffix(signal.length() - i);
            if (!suffix.isEmpty()) {
                RoSI subResult = subFml.getRoSI(suffix);
                if (subResult != null) {
                    result.assignMin(subResult);
                }
            }
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSIRawWithLen(IOSignal<I> signal, int length) {
        RoSI result = new RoSI(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY);
        int end = Math.min(length, signal.length());
        for (int i = 0; i < end; i++) {
            // suffix(n) returns the last n elements, so for position i we need suffix(length - i)
            IOSignal<I> suffix = signal.suffix(signal.length() - i);
            if (!suffix.isEmpty()) {
                RoSI subResult = subFml.getRoSI(suffix);
                if (subResult != null) {
                    result.assignMin(subResult);
                }
            }
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return "[] ( " + subFml.toString() + " )";
    }

    @Override
    public String toOwlString() {
        return String.format("G ( %s )", subFml.toOwlString());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toAbstractString() {
        return "[] ( " + subFml.toAbstractString() + " )";
    }

    @Override
    public TemporalLogic<I> toNnf(boolean negate){
        if (negate){
            return new TemporalEventually<>(subFml.toNnf(negate));
        } else {
            return new TemporalGlobally<>(subFml.toNnf(negate));
        }
    }

    @Override
    public TemporalLogic<I> toDisjunctiveForm(){
        return new TemporalGlobally<>(subFml.toDisjunctiveForm());
    }

    @Override
    public List<TemporalLogic<I>> getAllConjunctions(){
        return subFml.getAllConjunctions();
    }

    public static class STLGlobally extends TemporalGlobally<List<Double>> implements STLCost {
        public STLGlobally(STLCost subFml) {
            super(subFml);
        }
    }

    static class LTLGlobally extends TemporalGlobally<String> implements LTLFormula {
        private final LTLFormulaBase formulaBase = new LTLFormulaBase();
        
        LTLGlobally(LTLFormula subFml) {
            super(subFml);
        }
        
        @Override
        public void setAPs(LTLAPs aps) {
            formulaBase.setAPsWithPropagation(aps, () -> {
                if (subFml instanceof LTLFormula) {
                    ((LTLFormula) subFml).setAPs(aps);
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
