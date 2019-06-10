package org.group_mmm;

import java.util.Set;

abstract class STLTemporalOp extends STLCost {
    STLCost subFml;

    STLTemporalOp(STLCost subFml) {
        this.subFml = subFml;
        this.nonTemporal = false;
    }

    @Override
    protected void constructAtomicStrings() {
        this.atomicStrings = null;
    }

    @Override
    protected Set<String> getAllAPs() {
        return subFml.getAllAPs();
    }
}
