package net.maswag.falcaun.parser;

import java.util.Set;

import net.maswag.falcaun.IOSignal;

public abstract class TemporalOp<I> extends AbstractTemporalLogic<I> {
    TemporalLogic<I> subFml;

    TemporalOp(TemporalLogic<I> subFml) {
        this.subFml = subFml;
        this.nonTemporal = false;
        this.iOType = subFml.getIOType();
        this.initialized = subFml.isInitialized();
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
    public void constructSatisfyingAtomicPropositions() {
        super.constructSatisfyingAtomicPropositions();
        this.satisfyingAtomicPropositions = null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Set<String> getAllAPs() {
        return subFml.getAllAPs();
    }
}
