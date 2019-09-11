package org.group_mmm;

import net.automatalib.words.Word;

import java.util.List;
import java.util.Set;

abstract class STLTemporalOp extends STLCost {
    STLCost subFml;

    STLTemporalOp(STLCost subFml) {
        this.subFml = subFml;
        this.nonTemporal = false;
    }

    abstract public RoSI getRoSIRaw(Word<List<Double>> signal);

    @Override
    protected void constructAtomicStrings() {
        this.atomicStrings = null;
    }

    @Override
    protected Set<String> getAllAPs() {
        return subFml.getAllAPs();
    }
}
