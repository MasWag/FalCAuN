package net.maswag.falcaun;

import lombok.Getter;

import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * <p>TemporalUntil class.</p>
 * <p>This class implements the until operator in STL and LTL.</p>
 *
 * @param <I> Type of the input at each step
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Getter
public class TemporalUntil<I> extends AbstractTemporalLogic<I> {
    final private TemporalLogic<I> left, right;

    TemporalUntil(TemporalLogic<I> left, TemporalLogic<I> right) {
        this.left = left;
        this.right = right;
        this.nonTemporal = false;
        this.iOType = left.getIOType().merge(right.getIOType());
        this.initialized = left.isInitialized() && right.isInitialized();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal<I> signal) {
        return getRoSIRaw(signal).assignMax(new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY));
    }

    public RoSI getRoSIRaw(IOSignal<I> signal) {
        // The semantics of p U q is max_i (q_i && (p_0 && p_1 && ... && p_i)),
        // where p_i is the RoSI of the left formula at the i-th prefix of the signal,
        // and q_i is the RoSI of the right formula at the i-th prefix of the signal.
        RoSI result = new RoSI(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY);

        // Take the suffixes of signal in the longest-first order and compute their RoSI.
        List<RoSI> historyRoSIs = signal.suffixes(true).stream().map(this.left::getRoSI).toList();
        for (int i = 0; i < signal.length(); i++) {
            // Compute q_i && (p_0 && p_1 && ... && p_i)
            RoSI releasedRoSI = this.right.getRoSI(signal.subWord(i));
            RoSI reducedRoSI = historyRoSIs.stream().limit(i + 1)
                    .filter(Objects::nonNull)
                    .reduce(releasedRoSI, RoSI::min);

            result.assignMax(reducedRoSI);
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return this.left + " U " + this.right;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void constructSatisfyingAtomicPropositions() {
        super.constructSatisfyingAtomicPropositions();
        this.satisfyingAtomicPropositions = null;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public Set<String> getAllAPs() {
        Set<String> allAPs = this.left.getAllAPs();
        allAPs.addAll(this.right.getAllAPs());
        return allAPs;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toAbstractString() {
        return "( " + this.left.toAbstractString() + " ) U ( " + this.right.toAbstractString() + " )";
    }

    static class STLUntil extends TemporalUntil<List<Double>> implements STLCost {
        STLUntil(STLCost left, STLCost right) {
            super(left, right);
        }

        @Override
        public STLCost getLeft() {
            return (STLCost) super.getLeft();
        }

        @Override
        public STLCost getRight() {
            return (STLCost) super.getRight();
        }
    }

    static class LTLUntil extends TemporalUntil<String> implements LTLFormula {
        private final LTLFormulaBase formulaBase = new LTLFormulaBase();
        
        LTLUntil(TemporalLogic<String> left, TemporalLogic<String> right) {
            super(left, right);
        }
        
        @Override
        public void setAPs(LTLAPs aps) {
            formulaBase.setAPsWithPropagation(aps, () -> {
                if (getLeft() instanceof LTLFormula) {
                    ((LTLFormula) getLeft()).setAPs(aps);
                }
                if (getRight() instanceof LTLFormula) {
                    ((LTLFormula) getRight()).setAPs(aps);
                }
            });
        }
            
        
        @Override
        public LTLAPs getAPs() {
            return formulaBase.getAps();
        }
        
        @Override
        public void collectAtomicPropositions(LTLAPs aps) {
            if (getLeft() instanceof LTLFormula) {
                ((LTLFormula) getLeft()).collectAtomicPropositions(aps);
            }
            if (getRight() instanceof LTLFormula) {
                ((LTLFormula) getRight()).collectAtomicPropositions(aps);
            }
        }
    }
}
