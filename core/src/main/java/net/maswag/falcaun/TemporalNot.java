package net.maswag.falcaun;

import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * <p>STLTemporalNot class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 * @param <I> Type of the input at each step
 */
public class TemporalNot<I> extends AbstractTemporalLogic<I> {
    protected final TemporalLogic<I> subFml;

    /**
     * Constructs a new TemporalNot with the specified sub formula.
     *
     * @param subFml the sub formula
     */
    TemporalNot(TemporalLogic<I> subFml) {
        this.subFml = subFml;
        this.nonTemporal = subFml.isNonTemporal();
        this.iOType = subFml.getIOType();
        this.initialized = subFml.isInitialized();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal<I> signal) {
        return subFml.getRoSI(signal).assignNegate();
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
                this.satisfyingAtomicPropositions.removeAll(
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
        return subFml.getAllAPs();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toAbstractString() {
        return String.format("!( %s )", subFml.toAbstractString());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return String.format("!( %s )", subFml.toString());
    }

    @Override
    public String toOwlString(){
        return String.format("!( %s )", subFml.toOwlString());
    }
    
    @Override
    public TemporalLogic<I> toNnf(boolean negate){
        return subFml.toNnf(!negate);
    }

    @Override
    public TemporalLogic<I> toDisjunctiveForm(){
        return new TemporalNot<>(subFml.toDisjunctiveForm());
    }

    @Override
    public List<TemporalLogic<I>> getAllConjunctions(){
        return subFml.getAllConjunctions();
    }

    static class STLNot extends TemporalNot<List<Double>> implements STLCost {
        STLNot(STLCost subFml) {
            super(subFml);
        }
    }

    static class LTLNot extends TemporalNot<String> implements LTLFormula {
        private final LTLFormulaBase formulaBase = new LTLFormulaBase();
        
        LTLNot(LTLFormula subFml) {
            super(subFml);
        }
        
        @Override
        public void setAPs(LTLAPs aps) {
            formulaBase.setAPsWithPropagation(aps, () -> {
                // Propagate to subformula
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
        
        @Override
        public Set<String> getAllAPs() {
            LTLAPs aps = formulaBase.getAps();
            if (aps != null) {
                // Get the appropriate set from universe based on IOType
                if (this.iOType == IOType.INPUT) {
                    return aps.getInputAPs();
                } else if (this.iOType == IOType.OUTPUT) {
                    return aps.getOutputAPs();
                }
            }
            // Fallback to subformula's APs
            return subFml.getAllAPs();
        }
    }
}
