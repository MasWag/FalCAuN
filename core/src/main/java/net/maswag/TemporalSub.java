package net.maswag;

import lombok.Getter;
import lombok.extern.slf4j.Slf4j;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

@Getter
@Slf4j
public class TemporalSub<I> extends AbstractTemporalLogic<I> {
    private final TemporalOp<I> subFml;
    private final int from, to;

    /**
     * @param subFml the subformula
     * @param from   the first index, inclusive
     * @param to     the last index, inclusive.
     */
    TemporalSub(TemporalOp<I> subFml, int from, int to) {
        this.subFml = subFml;
        this.from = from;
        this.to = to;
        this.nonTemporal = false;
    }

    @Override
    public RoSI getRoSI(IOSignal<I> signal) {
        if (from >= signal.size()) {
            // If the signal is too short
            return new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY);
        } else if (to + 1 > signal.size()) {
            // If we do not know the window entirely.
            return subFml.getRoSI(signal.subWord(from, Math.min(to + 1, signal.size())));
        } else {
            // If we DO know the window entirely.
            return subFml.getRoSIRawWithLen(signal.subWord(from, signal.size()), to - from + 1);
        }
    }

    @Override
    public Set<String> getAllAPs() {
        return subFml.getAllAPs();
    }

    @Override
    public String toString() {
        String result = (subFml instanceof TemporalEventually) ? " <>" : " []";
        result += "_[" + (from) + ", " + (to) + "]";
        result += " ( " + (subFml.subFml.toString()) + " )";

        return result;
    }

    @Override
    public void constructAtomicStrings() {
        this.atomicStrings = null;
    }

    @Override
    public String toAbstractString() {
        final String op = (subFml.getClass().toString().equals("class net.maswag.STLEventually")) ? " || " : " && ";

        ArrayList<String> subFmls = new ArrayList<>();
        for (int i = this.from; i <= this.to; i++) {
            StringBuilder builder = new StringBuilder();
            builder.append("( ");

            for (int j = 0; j < i; j++) {
                builder.append("X (");
            }

            builder.append(subFml.subFml.toAbstractString());

            for (int j = 0; j < i; j++) {
                builder.append(" )");
            }
            builder.append(" )");

            subFmls.add(builder.toString());
        }

        return String.join(op, subFmls);
    }

    static class STLSub extends TemporalSub<List<Double>> implements STLCost {
        STLSub(TemporalOp<List<Double>> subFml, int from, int to) {
            super(subFml, from, to);
        }
    }

    static class LTLSub extends TemporalSub<String> implements LTLFormula {
        LTLSub(TemporalOp<String> subFml, int from, int to) {
            super(subFml, from, to);
        }
    }
}
