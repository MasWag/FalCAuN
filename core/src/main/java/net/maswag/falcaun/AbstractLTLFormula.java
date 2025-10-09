package net.maswag.falcaun;

/**
 * Abstract base class for LTL formulas that provides common functionality
 * for atomic propositions management.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public abstract class AbstractLTLFormula extends AbstractTemporalLogic<String> implements TemporalLogic.LTLFormula {
    protected LTLAPs aps;

    /**
     * {@inheritDoc}
     */
    @Override
    public void setAPs(LTLAPs aps) {
        this.aps = aps;
        // Propagate to subformulas
        propagateAPsToSubformulas(aps);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public LTLAPs getAPs() {
        return aps;
    }

    /**
     * Propagates the atomic propositions to all subformulas.
     * Subclasses should override this to propagate to their specific subformulas.
     *
     * @param aps The atomic propositions to propagate
     */
    protected void propagateAPsToSubformulas(LTLAPs aps) {
        // Default implementation does nothing
        // Subclasses with subformulas should override this
    }
}