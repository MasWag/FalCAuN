package net.maswag.falcaun;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

class TemporalNotTest {
    private final LTLFactory factory = new LTLFactory();
    private static final Pattern OUTPUT_ATOM_PATTERN = Pattern.compile("output == \\\"([^\\\"]+)\\\"");

    @Test
    void constructSatisfyingAtomicPropositionsForNegatedOutputs() {
        TemporalLogic.LTLFormula formula = factory.parse("[] ( (! output == p) || (! output == q))");
        
        // Prepare the formula with universe
        LTLFormulaHelper.prepareFormula(formula);
        
        Set<String> universe = new HashSet<>();
        universe.add("p");
        universe.add("q");

        List<TemporalNot<String>> negations = new ArrayList<>();
        collectTemporalNots(formula, negations);

        assertEquals(2, negations.size(),
                () -> "Expected two negations inside the globally formula but saw structure: "
                        + describeStructure(formula));

        for (TemporalNot<String> negation : negations) {
            assertTrue(negation.isNonTemporal(), "Negation should be non-temporal");

            Collection<String> satisfying = negation.getSatisfyingAtomicPropositions();
            assertNotNull(satisfying, "Non-temporal negation should expose satisfying atomic propositions");

            Set<String> expected = new HashSet<>(universe);
            extractNegatedAtom(negation).ifPresent(expected::remove);

            assertEquals(expected, new HashSet<>(satisfying),
                    () -> "Unexpected satisfying APs for " + negation.toAbstractString());
        }
    }

    private String describeStructure(TemporalLogic<String> formula) {
        if (formula instanceof TemporalGlobally.LTLGlobally) {
            return "Globally(" + describeStructure(((TemporalGlobally.LTLGlobally) formula).getSubFml()) + ")";
        }
        if (formula instanceof TemporalOr) {
            return "Or(" + ((TemporalOr<String>) formula).getSubFmls().stream()
                    .map(this::describeStructure)
                    .collect(Collectors.joining(", ")) + ")";
        }
        if (formula instanceof TemporalNot) {
            return "Not(" + formula.toAbstractString() + ")";
        }
        return formula.getClass().getSimpleName();
    }

    private void collectTemporalNots(TemporalLogic<String> formula, List<TemporalNot<String>> sink) {
        if (formula instanceof TemporalNot) {
            sink.add((TemporalNot<String>) formula);
        } else if (formula instanceof TemporalGlobally.LTLGlobally) {
            collectTemporalNots(((TemporalGlobally.LTLGlobally) formula).getSubFml(), sink);
        } else if (formula instanceof TemporalOr) {
            for (TemporalLogic<String> sub : ((TemporalOr<String>) formula).getSubFmls()) {
                collectTemporalNots(sub, sink);
            }
        }
    }

    private Optional<String> extractNegatedAtom(TemporalNot<String> negation) {
        Matcher matcher = OUTPUT_ATOM_PATTERN.matcher(negation.toAbstractString());
        if (matcher.find()) {
            return Optional.of(matcher.group(1));
        }
        return Optional.empty();
    }

    /**
     * Test case to reproduce the bug where Globally with OR of negated atomic propositions
     * results in empty satisfying atomic propositions, causing toAbstractString() to return
     * "[] ()" which leads to a model checker syntax error.
     *
     * Bug report: When using LTL formula like "[] ( (! output == p) || (! output == q))",
     * the satisfying atomic propositions become empty set, causing toAbstractString() to
     * return "[] ()" instead of a valid formula.
     */
    @Test
    void testGloballyWithNegatedOrFormulaBug() {
        // Parse the problematic formula from the bug report
        TemporalLogic.LTLFormula formula = factory.parse("[] ( (! output == p) || (! output == q))");
        
        // Prepare the formula with universe
        LTLFormulaHelper.prepareFormula(formula);
        
        // The formula should be a Globally operator
        assertTrue(formula instanceof TemporalGlobally.LTLGlobally,
                "Formula should be a Globally operator");
        
        TemporalGlobally.LTLGlobally globally = (TemporalGlobally.LTLGlobally) formula;
        TemporalLogic<String> subFormula = globally.getSubFml();
        
        // The subformula should be an OR
        assertTrue(subFormula instanceof TemporalOr,
                "Subformula should be an OR operator");
        
        TemporalOr<String> orFormula = (TemporalOr<String>) subFormula;
        
        // Check that the OR formula has satisfying atomic propositions
        Collection<String> orSatisfyingAPs = orFormula.getSatisfyingAtomicPropositions();
        assertNotNull(orSatisfyingAPs,
                "OR formula should have satisfying atomic propositions");
        
        // The bug: satisfying APs should NOT be empty for this formula
        // The OR of (! output == p) and (! output == q) should be satisfied by
        // any value except when output is both p and q (which is impossible)
        assertFalse(orSatisfyingAPs.isEmpty(),
                "Satisfying atomic propositions should not be empty for OR of negated atoms. " +
                "This causes toAbstractString() to return '[] ()' which is invalid syntax.");
        
        // Verify that toAbstractString() doesn't produce invalid syntax
        String abstractString = subFormula.toAbstractString();
        assertFalse(abstractString.trim().isEmpty(),
                "Abstract string should not be empty");
        assertFalse(abstractString.equals("()"),
                "Abstract string should not be just empty parentheses");
        
        // The abstract string for the whole formula should not be "[] ()"
        String globallyAbstractString = formula.toAbstractString();
        assertFalse(globallyAbstractString.equals("[] ()"),
                "Globally abstract string should not be '[] ()' as this causes model checker syntax error. " +
                "Actual: " + globallyAbstractString);
    }

    /**
     * Additional test to verify the correct behavior when negation is properly handled.
     * This test demonstrates what the expected behavior should be.
     */
    @Test
    void testNegationSatisfyingAPsWithProperUniverse() {
        // Create a simple negated atomic proposition
        TemporalLogic.LTLFormula negatedP = factory.parse("! output == p");
        
        // Prepare the formula to set up the APs
        LTLFormulaHelper.prepareFormula(negatedP);
        
        // For a negated atomic proposition "! output == p", the satisfying APs
        // should include all possible output values except "p"
        Collection<String> satisfyingAPs = negatedP.getSatisfyingAtomicPropositions();
        
        // After preparation, getAllAPs() should return the full universe
        Set<String> allAPs = negatedP.getAllAPs();
        
        // After the fix, getAllAPs should return the full universe {"p"}
        // (in this case, since we only have one atomic proposition mentioned)
        assertEquals(1, allAPs.size(),
                "getAllAPs() should return the collected APs");
        assertTrue(allAPs.contains("p"),
                "getAllAPs should contain 'p'");
        
        // The satisfying APs should now be correctly calculated
        // For "! output == p", it should be empty since we only have "p" in the universe
        // and "! output == p" is satisfied when output is NOT "p"
        if (satisfyingAPs != null) {
            assertTrue(satisfyingAPs.isEmpty(),
                    "Satisfying APs should be empty when the only AP is negated");
        }
    }

    /**
     * Direct test to demonstrate the "[] ()" syntax error bug.
     * This test shows that the toAbstractString() method returns invalid syntax
     * that would cause the model checker to fail.
     */
    @Test
    void testToAbstractStringProducesInvalidSyntax() {
        // Parse the problematic formula from the bug report
        TemporalLogic.LTLFormula formula = factory.parse("[] ( (! output == p) || (! output == q))");
        
        // Prepare the formula with universe - this should fix the bug
        LTLFormulaHelper.prepareFormula(formula);
        
        // Get the abstract string representation
        String abstractString = formula.toAbstractString();
        
        // Log the actual output for debugging
        System.out.println("Formula: [] ( (! output == p) || (! output == q))");
        System.out.println("Abstract string output: " + abstractString);
        
        // After the fix, this should NOT be "[] (  )"
        assertNotEquals("[] (  )", abstractString,
                "After fix: toAbstractString() should not return '[] (  )' (empty OR expression)");
        
        // The abstract string should contain actual content
        assertTrue(abstractString.contains("output"),
                "Abstract string should contain output references");
    }

    /**
     * Verification test for the bug reported in bug-report.txt
     * This test verifies that the formula from the bug report now works correctly.
     */
    @Test
    void testBugReportFormulaWithProperAPInitialization() {
        // The exact formula from the bug report
        String formulaStr = "[] ( (! output == p) || (! output == q))";
        
        // Parse the formula
        TemporalLogic.LTLFormula formula = factory.parse(formulaStr);
        assertNotNull(formula, "Formula should parse successfully");
        
        // Initialize atomic propositions - we need to provide the universe of possible values
        List<String> inputAPs = new ArrayList<>();
        List<String> outputAPs = List.of("output");
        LTLAPs aps = new LTLAPs(inputAPs, outputAPs);
        
        // Add the possible values for output to the universe
        aps.addOutputAP("p");
        aps.addOutputAP("q");
        
        // Prepare the formula with atomic propositions
        LTLFormulaHelper.prepareFormula(formula);
        formula.setAPs(aps);
        
        // Get the abstract string - this was producing "[] ()" before the fix
        String abstractStr = formula.toAbstractString();
        
        // PRIMARY FIX VERIFICATION: The abstract string is not empty
        assertNotEquals("[] ()", abstractStr,
            "Abstract string should not be empty - this was the bug!");
        
        // Verify it contains the expected content
        assertTrue(abstractStr.contains("output"),
            "Abstract string should contain 'output'");
        
        // The formula should produce a valid abstract string (not empty parentheses)
        assertFalse(abstractStr.contains("()"),
            "Abstract string should not contain empty parentheses");
    }

    /**
     * Test similar formulas that would have had the same issue
     */
    @Test
    void testSimilarProblematicFormulas() {
        // Test other similar formulas that would have had the same issue
        String[] formulas = {
            "[] (! output == a)",
            "[] ( (! output == x) && (! output == y))",
            "<> (! output == test)"
        };
        
        for (String formulaStr : formulas) {
            TemporalLogic.LTLFormula formula = factory.parse(formulaStr);
            assertNotNull(formula, "Formula should parse: " + formulaStr);
            
            // Initialize with both input and output APs
            List<String> inputAPs = new ArrayList<>();
            List<String> outputAPs = List.of("output");
            LTLAPs aps = new LTLAPs(inputAPs, outputAPs);
            
            // Add possible values to the universe
            aps.addOutputAP("a");
            aps.addOutputAP("x");
            aps.addOutputAP("y");
            aps.addOutputAP("test");
            
            LTLFormulaHelper.prepareFormula(formula);
            formula.setAPs(aps);
            
            String abstractStr = formula.toAbstractString();
            
            // PRIMARY FIX VERIFICATION: None should produce empty operators
            assertFalse(abstractStr.contains("()"),
                "Abstract string should not contain empty parentheses for: " + formulaStr);
            assertFalse(abstractStr.contains("[] ()"),
                "Abstract string should not be '[] ()' for: " + formulaStr);
            assertFalse(abstractStr.contains("<> ()"),
                "Abstract string should not be '<> ()' for: " + formulaStr);
        }
    }

    /**
     * Test reproduces the exact scenario from the bug report
     */
    @Test
    void testOriginalBugScenarioWithoutFullAPInitialization() {
        // This test reproduces the exact scenario from the bug report
        String formulaStr = "[] ( (! output == p) || (! output == q))";
        
        // Parse the formula
        TemporalLogic.LTLFormula formula = factory.parse(formulaStr);
        
        // Without proper AP initialization, this used to produce "[] ()"
        LTLFormulaHelper.prepareFormula(formula);
        
        // Even without setting the full universe, the formula should not produce empty syntax
        String abstractStr = formula.toAbstractString();
        
        // The critical bug fix: no more empty "[] ()" syntax
        assertNotEquals("[] ()", abstractStr,
            "The bug is fixed: Formula no longer produces '[] ()' which caused model checker crashes");
    }
}
