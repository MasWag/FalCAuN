package org.group_mmm;

abstract class STLTemporalOp extends STLCost {
    STLCost subFml;

    STLTemporalOp(STLCost subFml) {
        this.subFml = subFml;
    }
}
