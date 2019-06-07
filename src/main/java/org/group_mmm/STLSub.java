package org.group_mmm;

import com.sun.istack.internal.NotNull;
import net.automatalib.words.Word;

import java.util.ArrayList;

public class STLSub extends STLCost {
    private STLCost subFml;
    private int from, to;

    public STLSub(STLCost subFml, int from, int to) {
        this.subFml = subFml;
        this.from = from;
        this.to = to;
    }

    @Override
    @NotNull
    public Double apply(Word<ArrayList<Double>> signal) {
        if (from >= signal.size()) {
            return null;
        }
        return subFml.apply(signal.subWord(from, Math.min(to, signal.size() - 1)));
    }
}
