package org.group_mmm;

import ch.qos.logback.classic.Logger;
import net.automatalib.words.Word;
import org.jetbrains.annotations.NotNull;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.Set;

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

    @Override
    @NotNull
    public Double apply(Word<ArrayList<Double>> signal) {
        if (from >= signal.size()) {
            switch (subFml.getClass().toString()) {
                case "class org.group_mmm.STLEventually":
                    return Double.NEGATIVE_INFINITY;
                case "class org.group_mmm.STLGlobal":
                    return Double.POSITIVE_INFINITY;
                default:
                    LOGGER.error("Unknown class {}", subFml.getClass());
            }
        }
        return subFml.apply(signal.subWord(from, Math.min(to + 1, signal.size())));
    }

    @Override
    protected Set<String> getAllAPs() {
        return subFml.getAllAPs();
    }

    @Override
    public String toString() {
        final String op = (subFml.getClass().toString().equals("class org.group_mmm.STLEventually")) ? " || " : " && ";

        ArrayList<String> subFmls = new ArrayList<>();
        for (int i = this.from; i <= this.to; i++) {
            StringBuilder builder = new StringBuilder();
            builder.append("( ");

            for (int j = 0; j < i; j++) {
                builder.append("X (");
            }

            builder.append(subFml.subFml.toString());

            for (int j = 0; j < i; j++) {
                builder.append(" )");
            }
            builder.append(" )");

            subFmls.add(builder.toString());
        }

        return String.join(op, subFmls);
    }

    @Override
    protected void constructAtomicStrings() {
        this.atomicStrings = null;
    }

    @Override
    String toAbstractString() {
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
