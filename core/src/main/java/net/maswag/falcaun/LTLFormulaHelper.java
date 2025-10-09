package net.maswag.falcaun;

/**
 * Helper class for LTL formula operations.
 */
public class LTLFormulaHelper {
    
    /**
     * Collects all atomic propositions from a formula tree and creates an APs collection.
     *
     * @param formula The root formula
     * @return An LTLAPs containing all atomic propositions found in the formula
     */
    public static LTLAPs collectAPs(TemporalLogic.LTLFormula formula) {
        LTLAPs aps = new LTLAPs();
        collectAtomicPropositionsRecursive(formula, aps);
        return aps;
    }
    
    /**
     * Sets the atomic propositions on a formula tree and propagates it to all subformulas.
     *
     * @param formula The root formula
     * @param aps The atomic propositions to set
     */
    public static void setAPs(TemporalLogic.LTLFormula formula, LTLAPs aps) {
        if (formula instanceof LTLAtomic) {
            formula.setAPs(aps);
        } else if (formula instanceof TemporalNot.LTLNot) {
            formula.setAPs(aps);
        } else if (formula instanceof TemporalOr.LTLOr) {
            formula.setAPs(aps);
        } else if (formula instanceof TemporalAnd.LTLAnd and) {
            and.setAPs(aps);
        } else if (formula instanceof TemporalGlobally.LTLGlobally globally) {
            globally.setAPs(aps);
        } else if (formula instanceof TemporalEventually.LTLEventually eventually) {
            eventually.setAPs(aps);
        } else if (formula instanceof TemporalUntil.LTLUntil until) {
            until.setAPs(aps);
        } else if (formula instanceof TemporalRelease.LTLRelease release) {
            release.setAPs(aps);
        } else if (formula instanceof TemporalNext.LTLNext next) {
            next.setAPs(aps);
        } else if (formula instanceof TemporalImply.LTLImply imply) {
            imply.setAPs(aps);
        } else if (formula instanceof TemporalSub.LTLSub sub) {
            sub.setAPs(aps);
        }
    }
    
    /**
     * Prepares a formula for use by collecting its atomic propositions and setting them.
     *
     * @param formula The formula to prepare
     * @return The same formula with atomic propositions set
     */
    public static TemporalLogic.LTLFormula prepareFormula(TemporalLogic.LTLFormula formula) {
        LTLAPs aps = collectAPs(formula);
        setAPs(formula, aps);
        return formula;
    }
    
    private static void collectAtomicPropositionsRecursive(Object formula, LTLAPs aps) {
        if (formula instanceof LTLAtomic) {
            ((LTLAtomic) formula).collectAtomicPropositions(aps);
        } else if (formula instanceof TemporalNot<?> not) {
            collectAtomicPropositionsRecursive(not.subFml, aps);
        } else if (formula instanceof TemporalOr<?> or) {
            for (TemporalLogic<?> subFml : or.getSubFmls()) {
                collectAtomicPropositionsRecursive(subFml, aps);
            }
        } else if (formula instanceof TemporalAnd<?> and) {
            for (TemporalLogic<?> subFml : and.getSubFormulas()) {
                collectAtomicPropositionsRecursive(subFml, aps);
            }
        } else if (formula instanceof TemporalGlobally<?> globally) {
            collectAtomicPropositionsRecursive(globally.getSubFml(), aps);
        } else if (formula instanceof TemporalEventually<?> eventually) {
            collectAtomicPropositionsRecursive(eventually.getSubFml(), aps);
        } else if (formula instanceof TemporalUntil<?> until) {
            collectAtomicPropositionsRecursive(until.getLeft(), aps);
            collectAtomicPropositionsRecursive(until.getRight(), aps);
        } else if (formula instanceof TemporalRelease<?> release) {
            collectAtomicPropositionsRecursive(release.getLeft(), aps);
            collectAtomicPropositionsRecursive(release.getRight(), aps);
        } else if (formula instanceof TemporalNext<?> next) {
            collectAtomicPropositionsRecursive(next.getSubFml(), aps);
        } else if (formula instanceof TemporalImply<?> imply) {
            collectAtomicPropositionsRecursive(imply, aps);
        } else if (formula instanceof TemporalSub<?> sub) {
            collectAtomicPropositionsRecursive(sub, aps);
        }
    }
}