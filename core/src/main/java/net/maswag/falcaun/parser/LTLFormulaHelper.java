package net.maswag.falcaun.parser;

import net.maswag.falcaun.LTLAPs;

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
            handleAtomicFormula((LTLAtomic) formula, aps);
        } else if (formula instanceof TemporalNot<?> not) {
            handleUnaryOperator(not.subFml, aps);
        } else if (formula instanceof TemporalOr<?> or) {
            handleMultiaryOperator(or.getSubFmls(), aps);
        } else if (formula instanceof TemporalAnd<?> and) {
            handleMultiaryOperator(and.getSubFormulas(), aps);
        } else if (formula instanceof TemporalGlobally<?> globally) {
            handleUnaryOperator(globally.getSubFml(), aps);
        } else if (formula instanceof TemporalEventually<?> eventually) {
            handleUnaryOperator(eventually.getSubFml(), aps);
        } else if (formula instanceof TemporalUntil<?> until) {
            handleBinaryOperator(until.getLeft(), until.getRight(), aps);
        } else if (formula instanceof TemporalRelease<?> release) {
            handleBinaryOperator(release.getLeft(), release.getRight(), aps);
        } else if (formula instanceof TemporalNext<?> next) {
            handleUnaryOperator(next.getSubFml(), aps);
        } else if (formula instanceof TemporalImply<?> imply) {
            handleBinaryOperator(imply.getSubFml1(), imply.getSubFml2(), aps);
        } else if (formula instanceof TemporalSub<?> sub) {
            handleUnaryOperator(sub.getSubFml(), aps);
        }
    }
    
    /**
     * Handles atomic formulas by collecting their atomic propositions.
     */
    private static void handleAtomicFormula(LTLAtomic atomic, LTLAPs aps) {
        atomic.collectAtomicPropositions(aps);
    }
    
    /**
     * Handles unary operators (operators with a single subformula).
     */
    private static void handleUnaryOperator(Object subFormula, LTLAPs aps) {
        collectAtomicPropositionsRecursive(subFormula, aps);
    }
    
    /**
     * Handles binary operators (operators with two subformulas).
     */
    private static void handleBinaryOperator(Object leftFormula, Object rightFormula, LTLAPs aps) {
        collectAtomicPropositionsRecursive(leftFormula, aps);
        collectAtomicPropositionsRecursive(rightFormula, aps);
    }
    
    /**
     * Handles multiary operators (operators with multiple subformulas).
     */
    private static void handleMultiaryOperator(Iterable<? extends TemporalLogic<?>> subFormulas, LTLAPs aps) {
        for (TemporalLogic<?> subFml : subFormulas) {
            collectAtomicPropositionsRecursive(subFml, aps);
        }
    }
    
}
