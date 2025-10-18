package net.maswag.falcaun.parser;

import java.util.ArrayList;

import lombok.Getter;
import net.maswag.falcaun.IOSignal;

import java.util.List;
import java.util.Objects;
import java.util.Set;

import net.maswag.falcaun.LTLAPs;
import net.maswag.falcaun.LTLFormulaBase;

/**
 * <p>TemporalRelease class.</p>
 * <p>This class implements the release operator in STL and LTL.</p>
 *
 * @param <I> Type of the input at each step
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Getter
public class TemporalRelease<I> extends AbstractTemporalLogic<I> {
    private final TemporalLogic<I> left, right;

    TemporalRelease(TemporalLogic<I> left, TemporalLogic<I> right) {
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
        return getRoSIRaw(signal).assignMin(new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY));
    }

    public RoSI getRoSIRaw(IOSignal<I> signal) {
        // The semantics of the Release operator (p R q) is:
        // min_i (q_i || (p_0 || p_1 || ... || p_i)),
        // where p_i is the RoSI of the left formula at the i-th prefix of the signal,
        // and q_i is the RoSI of the right formula at the i-th prefix of the signal.
        // This follows from the equivalence: p R q ≡ !((!p) U (!q)).
        RoSI result = new RoSI(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY);

        // Take the suffixes of signal in the longest-first order and compute their RoSI.
        List<RoSI> historyRoSIs = signal.suffixes(true).stream().map(this.left::getRoSI).toList();
        for (int i = 0; i < signal.length(); i++) {
            // Compute q_i || (p_0 || p_1 || ... || p_i)
            RoSI releasedRoSI = this.right.getRoSI(signal.subWord(i));
            RoSI reducedRoSI = historyRoSIs.stream().limit(i + 1)
                    .filter(Objects::nonNull)
                    .reduce(releasedRoSI, RoSI::max);
            result.assignMin(reducedRoSI);
        }
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return this.left + " R " + this.right;
    }

    @Override
    public String toOwlString() {
        return "( " + this.left.toOwlString() + " ) R ( " + this.right.toOwlString() + " )";
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
        return "( " + this.left.toAbstractString() + " ) R ( " + this.right.toAbstractString() + " )";
    }

    @Override
    public TemporalLogic<I> toNnf(boolean negate) {
        if (negate) {
            return new TemporalUntil<>(left.toNnf(negate), right.toNnf(negate));
        } else {
            return new TemporalRelease<>(left.toNnf(negate), right.toNnf(negate));
        }
    }

    @Override
    public TemporalLogic<I> toDisjunctiveForm() {
        return new TemporalRelease<>(left.toDisjunctiveForm(), right.toDisjunctiveForm());
    }

    @Override
    public List<TemporalLogic<I>> getAllConjunctions() {
        List<TemporalLogic<I>> result = new ArrayList<>();
        result.addAll(left.getAllConjunctions());
        result.addAll(right.getAllConjunctions());
        return result;
    }

    static class STLRelease extends TemporalRelease<List<Double>> implements STLCost {
        STLRelease(STLCost left, STLCost right) {
            super(left, right);
        }
    }

    static class LTLRelease extends TemporalRelease<String> implements LTLFormula {
        private final LTLFormulaBase formulaBase = new LTLFormulaBase();

        LTLRelease(LTLFormula left, LTLFormula right) {
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
