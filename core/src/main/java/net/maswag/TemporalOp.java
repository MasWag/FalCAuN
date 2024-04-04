package net.maswag;

import java.util.Set;

abstract class TemporalOp<I> extends AbstractTemporalLogic<I> {
    TemporalLogic<I> subFml;

    TemporalOp(TemporalLogic<I> subFml) {
        this.subFml = subFml;
        this.nonTemporal = false;
    }

    /**
     * <p>getRoSIRaw.</p>
     *
     * @param signal a {@link net.automatalib.word.Word} object.
     * @return a RoSI object.
     */
    abstract public RoSI getRoSIRaw(IOSignal<I> signal);

    /**
     * <p>getRoSIRawLen.</p>
     *
     * @param signal a {@link net.automatalib.word.Word} object.
     * @param length the length to compute the RoSI
     * @return a RoSI object.
     */
    abstract public RoSI getRoSIRawWithLen(IOSignal<I> signal, int length);

    /**
     * {@inheritDoc}
     */
    @Override
    public void constructAtomicStrings() {
        this.atomicStrings = null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Set<String> getAllAPs() {
        return subFml.getAllAPs();
    }
}
