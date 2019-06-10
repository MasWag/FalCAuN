package org.group_mmm;

import net.automatalib.words.Word;

import java.util.ArrayList;

import static java.lang.Math.abs;

public class STLAtomic extends STLCost {
    private Operation op;
    private int sigIndex;
    private double comparator;

    STLAtomic(int sigIndex, Operation op, double comparator) {
        this.sigIndex = sigIndex;
        this.comparator = comparator;
        this.op = op;
    }

    @Override
    public Double apply(Word<ArrayList<Double>> signal) {
        ArrayList<Double> currentValue = signal.getSymbol(0);
        if (signal.isEmpty() || currentValue == null) {
            return Double.POSITIVE_INFINITY;
        }
        switch (op) {
            case lt:
                return comparator - currentValue.get(sigIndex);
            case gt:
                return currentValue.get(sigIndex) - comparator;
            case eq:
                return abs(currentValue.get(sigIndex) - comparator);
            default:
                return null;
        }
    }

    enum Operation {
        lt,
        eq,
        gt
    }
}
