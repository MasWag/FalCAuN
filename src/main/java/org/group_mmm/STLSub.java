package org.group_mmm;

import ch.qos.logback.classic.Logger;
import net.automatalib.words.Word;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * <p>STLSub class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class STLSub extends STLCost {
    private final Logger LOGGER = (Logger) LoggerFactory.getLogger(STLSub.class);

    private STLTemporalOp subFml;
    private int from, to;

    /**
     * @param subFml the subformula
     * @param from   the first index, inclusive
     * @param to     the last index, inclusive.
     */
    STLSub(STLTemporalOp subFml, int from, int to) {
        this.subFml = subFml;
        this.from = from;
        this.to = to;
        this.nonTemporal = false;
    }

    /** {@inheritDoc} */
    @Override
    public RoSI getRoSI(Word<List<Double>> signal) {
        if (from >= signal.size()) {
            // If the signal is too short
            return new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY);
        } else if (to + 1 > signal.size()) {
            // If we do not know the window entirely.
            return subFml.getRoSI(signal.subWord(from, Math.min(to + 1, signal.size())));
        } else {
            // If we DO know the window entirely.
            return subFml.getRoSIRaw(signal.subWord(from, Math.min(to + 1, signal.size())));
        }
    }

    /** {@inheritDoc} */
    @Override
    protected Set<String> getAllAPs() {
        return subFml.getAllAPs();
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        String result = (subFml.getClass().toString().equals("class org.group_mmm.STLEventually")) ? " <>" : " []";
        result += "_[" + (from) + ", " + (to) + "]";
        result += " ( " + (subFml.subFml.toString()) + " )";

        return result;
    }

    /** {@inheritDoc} */
    @Override
    protected void constructAtomicStrings() {
        this.atomicStrings = null;
    }

    /** {@inheritDoc} */
    @Override
    public String toAbstractString() {
        final String op = (subFml.getClass().toString().equals("class org.group_mmm.STLEventually")) ? " || " : " && ";

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
}
