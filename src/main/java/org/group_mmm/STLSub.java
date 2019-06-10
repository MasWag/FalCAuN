package org.group_mmm;

import ch.qos.logback.classic.Logger;
import org.jetbrains.annotations.NotNull;
import net.automatalib.modelcheckers.ltsmin.AbstractLTSmin;
import net.automatalib.words.Word;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;

public class STLSub extends STLCost {
    private final Logger LOGGER = (Logger) LoggerFactory.getLogger(AbstractLTSmin.class);

    private STLTemporalOp subFml;
    private int from, to;

    STLSub(STLTemporalOp subFml, int from, int to) {
        this.subFml = subFml;
        this.from = from;
        this.to = to;
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
                    return null;
            }
        }
        return subFml.apply(signal.subWord(from, Math.min(to, signal.size() - 1)));
    }
}
