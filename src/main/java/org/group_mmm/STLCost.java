package org.group_mmm;

import net.automatalib.words.Word;

import java.util.ArrayList;
import java.util.Set;
import java.util.function.Function;

abstract class STLCost implements Function<Word<ArrayList<Double>>, Double> {
    boolean nonTemporal;
    Set<String> atomicStrings;

    Set<String> getAtomicStrings() {
        return atomicStrings;
    }

    public boolean isNonTemporal() {
        return nonTemporal;
    }

    protected abstract Set<String> getAllAPs();

    protected abstract void constructAtomicStrings();

    abstract String toAbstractString();
}
