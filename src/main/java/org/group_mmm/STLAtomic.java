package org.group_mmm;

import net.automatalib.words.Word;

import java.util.ArrayList;

public class STLAtomic extends STLCost {
    private int sigIndex;
    private double comparator;
    private boolean lt;

    STLAtomic(int sigIndex, boolean lt, double comparator) {
        this.sigIndex = sigIndex;
        this.comparator = comparator;
        this.lt = lt;
    }

    @Override
    public Double apply(Word<ArrayList<Double>> signal) {
        if (signal.isEmpty()) {
            return Double.POSITIVE_INFINITY;
        }
        return lt ? comparator - signal.getSymbol(0).get(sigIndex) :
                signal.getSymbol(0).get(sigIndex) - comparator;
    }
}
