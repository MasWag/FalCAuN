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

    /**
     * <p>getRoSIRaw.</p>
     *
     * @param signal a {@link net.automatalib.words.Word} object.
     * @return a RoSI object.
     */
    abstract public RoSI getRoSIRaw(Word<List<Double>> signal);

    /**
     * <p>getRoSIRawLen.</p>
     *
     * @param signal a {@link net.automatalib.words.Word} object.
     * @param length the length to compute the RoSI
     * @return a RoSI object.
     */
    abstract public RoSI getRoSIRawWithLen(Word<List<Double>> signal, int length);

    /**
     * {@inheritDoc}
     */
    @Override
    protected void constructAtomicStrings() {
        this.atomicStrings = null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Set<String> getAllAPs() {
        return subFml.getAllAPs();
    }
}
