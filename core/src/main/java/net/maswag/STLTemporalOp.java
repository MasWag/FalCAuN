package net.maswag;

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
    abstract public RoSI getRoSIRaw(IOSignal signal);

    /**
     * <p>getRoSIRawLen.</p>
     *
     * @param signal a {@link net.automatalib.words.Word} object.
     * @param length the length to compute the RoSI
     * @return a RoSI object.
     */
    abstract public RoSI getRoSIRawWithLen(IOSignal signal, int length);

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
