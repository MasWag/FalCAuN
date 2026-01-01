package net.maswag.falcaun.parser;

import net.maswag.falcaun.parser.TemporalLogic.LTLFormula;
import net.maswag.falcaun.parser.TemporalLogic.STLCost;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.*;

import static org.junit.jupiter.api.Assertions.*;

class LTLFormulaHelperTest {
    private List<Map<Character, Double>> inputMapper;
    private List<Map<Character, Double>> outputMapper;
    private List<Character> largest;
    private STLFactory stlFactory;

    @BeforeEach
    void setUp() {
        // Set up mappers for STL formula initialization
        Map<Character, Double> velocityMap = new HashMap<>();
        velocityMap.put('a', 20.0);
        velocityMap.put('b', 120.0);
        
        Map<Character, Double> rotationMap = new HashMap<>();
        rotationMap.put('a', -20.0);
        rotationMap.put('b', 4.2);
        
        Map<Character, Double> gearMap = new HashMap<>();
        gearMap.put('a', 2.0);
        gearMap.put('b', 3.0);
        
        inputMapper = Collections.emptyList();
        outputMapper = Arrays.asList(velocityMap, rotationMap, gearMap);
        largest = Arrays.asList('c', 'c', 'c');
        stlFactory = new STLFactory();
    }

    @Test
    void testConvertToLTLFormulasWithSimpleFormulas() {
        // Create STL formulas with proper initialization
        List<STLCost> stlFormulas = Arrays.asList(
                stlFactory.parse("[] ( output(0) < 120.0 )", inputMapper, outputMapper, largest),
                stlFactory.parse("<> ( output(0) > 20.0 )", inputMapper, outputMapper, largest)
        );

        // Convert to LTL formulas
        List<LTLFormula> ltlFormulas = LTLFormulaHelper.convertToLTLFormulas(stlFormulas);

        // Verify the conversion
        assertNotNull(ltlFormulas);
        assertEquals(2, ltlFormulas.size());
        
        // Verify each formula is properly prepared (APs are set)
        for (LTLFormula formula : ltlFormulas) {
            assertNotNull(formula);
            assertTrue(formula.isInitialized(), "Formula should be initialized after conversion");
        }
    }

    @Test
    void testConvertToLTLFormulasWithEmptyList() {
        // Test with empty list
        List<STLCost> emptyList = Collections.emptyList();
        List<LTLFormula> result = LTLFormulaHelper.convertToLTLFormulas(emptyList);

        assertNotNull(result);
        assertTrue(result.isEmpty());
    }

    @Test
    void testConvertToLTLFormulasWithQuotesInFormula() {
        // Create an STL formula that may have quotes in its LTL string representation
        STLCost stlFormula = stlFactory.parse("[] ( output(0) < 100.0 )", inputMapper, outputMapper, largest);
        List<STLCost> stlFormulas = Collections.singletonList(stlFormula);

        // Convert to LTL
        List<LTLFormula> ltlFormulas = LTLFormulaHelper.convertToLTLFormulas(stlFormulas);

        assertNotNull(ltlFormulas);
        assertEquals(1, ltlFormulas.size());
        
        LTLFormula ltlFormula = ltlFormulas.get(0);
        assertNotNull(ltlFormula);
        assertTrue(ltlFormula.isInitialized());
        
        // Verify the string representation doesn't contain quotes
        String ltlString = ltlFormula.toString();
        String expected = new LTLFactory().parse(stlFormula.toLTLString().replace("\"", "")).toString();
        assertNotNull(ltlString);
        assertEquals(expected, ltlString);
    }

    @Test
    void testConvertToLTLFormulasWithComplexFormula() {
        // Test with a complex STL formula involving multiple operators
        List<STLCost> stlFormulas = Arrays.asList(
                stlFactory.parse("[] ( ( output(0) < 100.0 ) -> ( output(1) > -20.0 ) )", inputMapper, outputMapper, largest),
                stlFactory.parse("( output(0) > 20.0 ) U ( output(1) < 4.2 )", inputMapper, outputMapper, largest)
        );

        List<LTLFormula> ltlFormulas = LTLFormulaHelper.convertToLTLFormulas(stlFormulas);

        assertNotNull(ltlFormulas);
        assertEquals(2, ltlFormulas.size());
        
        for (LTLFormula formula : ltlFormulas) {
            assertNotNull(formula);
            assertTrue(formula.isInitialized());
        }
    }

    @Test
    void testConvertToLTLFormulasWithMultipleGloballyOperators() {
        List<STLCost> stlFormulas = Arrays.asList(
                stlFactory.parse("[] ( output(0) < 120.0 )", inputMapper, outputMapper, largest),
                stlFactory.parse("[] ( output(1) > -20.0 )", inputMapper, outputMapper, largest),
                stlFactory.parse("[] ( output(2) == 2.0 )", inputMapper, outputMapper, largest)
        );

        List<LTLFormula> ltlFormulas = LTLFormulaHelper.convertToLTLFormulas(stlFormulas);

        assertNotNull(ltlFormulas);
        assertEquals(3, ltlFormulas.size());
        
        for (LTLFormula formula : ltlFormulas) {
            assertNotNull(formula);
            assertTrue(formula.isInitialized());
        }
    }

    @Test
    void testConvertToLTLFormulasWithEventuallyOperator() {
        List<STLCost> stlFormulas = Arrays.asList(
                stlFactory.parse("<> ( output(0) > 20.0 )", inputMapper, outputMapper, largest),
                stlFactory.parse("<> ( output(1) < 4.2 )", inputMapper, outputMapper, largest)
        );

        List<LTLFormula> ltlFormulas = LTLFormulaHelper.convertToLTLFormulas(stlFormulas);

        assertNotNull(ltlFormulas);
        assertEquals(2, ltlFormulas.size());
        
        for (LTLFormula formula : ltlFormulas) {
            assertNotNull(formula);
            assertTrue(formula.isInitialized());
        }
    }

    @Test
    void testConvertToLTLFormulasWithAndOperator() {
        List<STLCost> stlFormulas = Collections.singletonList(
                stlFactory.parse("( output(0) > 20.0 ) && ( output(1) < 4.2 )", inputMapper, outputMapper, largest)
        );

        List<LTLFormula> ltlFormulas = LTLFormulaHelper.convertToLTLFormulas(stlFormulas);

        assertNotNull(ltlFormulas);
        assertEquals(1, ltlFormulas.size());
        
        LTLFormula formula = ltlFormulas.get(0);
        assertNotNull(formula);
        assertTrue(formula.isInitialized());
    }

    @Test
    void testConvertToLTLFormulasWithOrOperator() {
        List<STLCost> stlFormulas = Collections.singletonList(
                stlFactory.parse("( output(0) > 20.0 ) || ( output(1) < 4.2 )", inputMapper, outputMapper, largest)
        );

        List<LTLFormula> ltlFormulas = LTLFormulaHelper.convertToLTLFormulas(stlFormulas);

        assertNotNull(ltlFormulas);
        assertEquals(1, ltlFormulas.size());
        
        LTLFormula formula = ltlFormulas.get(0);
        assertNotNull(formula);
        assertTrue(formula.isInitialized());
    }

    @Test
    void testConvertToLTLFormulasPreservesOrder() {
        // Test that the order of formulas is preserved
        List<STLCost> stlFormulas = Arrays.asList(
                stlFactory.parse("[] ( output(0) < 120.0 )", inputMapper, outputMapper, largest),
                stlFactory.parse("<> ( output(1) > -20.0 )", inputMapper, outputMapper, largest),
                stlFactory.parse("[] ( output(2) == 2.0 )", inputMapper, outputMapper, largest)
        );

        List<LTLFormula> ltlFormulas = LTLFormulaHelper.convertToLTLFormulas(stlFormulas);

        assertNotNull(ltlFormulas);
        assertEquals(3, ltlFormulas.size());

        LTLFactory ltlFactory = new LTLFactory();
        List<String> expectedOrder = stlFormulas.stream()
                .map(stl -> ltlFactory.parse(stl.toLTLString().replace("\"", "")).toString())
                .toList();
        
        for (int i = 0; i < ltlFormulas.size(); i++) {
            LTLFormula ltlFormula = ltlFormulas.get(i);
            assertNotNull(ltlFormula);
            assertEquals(expectedOrder.get(i), ltlFormula.toString());
            assertTrue(ltlFormula.isInitialized(),
                    "Formula at index " + i + " should be initialized");
        }
    }
}
