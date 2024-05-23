package net.maswag;

import java.util.List;
import java.util.Objects;

/**
 * <p>STLGlobal class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 * @param <I> Type of the input at each step
 */
public class TemporalGlobally<I> extends TemporalOp<I> {
    TemporalGlobally(TemporalLogic<I> subFml) {
        super(subFml);
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
    public RoSI getRoSIRaw(IOSignal<I> signal) {
        return signal.suffixes(true).stream().filter(w -> !w.isEmpty()).map(w -> subFml.getRoSI(w)).filter(Objects::nonNull)
                .reduce(new RoSI(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY), RoSI::min);
    }

    /**
     * {@inheritDoc}
     */
    public RoSI getRoSIRawWithLen(IOSignal<I> signal, int length) {
        return signal.suffixes(true).subList(0, length).stream().filter(w -> !w.isEmpty()).map(w -> subFml.getRoSI(w)).filter(Objects::nonNull)
                .reduce(new RoSI(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY), RoSI::min);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toAbstractString() {
        return String.format("[] ( %s )", subFml.toAbstractString());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return String.format("[] ( %s )", subFml.toString());
    }

    /**
     * <p>getSubFml.</p>
     *
     * @return a {@link TemporalLogic<I>} object.
     */
    public TemporalLogic<I> getSubFml() { return this.subFml; }

    static class STLGlobally extends TemporalGlobally<List<Double>> implements STLCost {
        STLGlobally(STLCost subFml) {
            super(subFml);
        }

        @Override
        public STLCost getSubFml() {
            return (STLCost) this.subFml;
        }
    }

    static class LTLGlobally extends TemporalGlobally<String> implements LTLFormula {
        LTLGlobally(LTLFormula subFml) {
            super(subFml);
        }
    }
}
