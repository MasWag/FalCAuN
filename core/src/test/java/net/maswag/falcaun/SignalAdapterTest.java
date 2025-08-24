package net.maswag.falcaun;

import net.automatalib.alphabet.Alphabet;
import net.automatalib.word.Word;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.*;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for the {@link SignalAdapter} class.
 * 
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
class SignalAdapterTest {

    private InputMapper inputMapper;
    private OutputMapper outputMapper;
    private SignalAdapter adapter;

    @BeforeEach
    void setUp() {
        // Create InputMapper
        List<List<Double>> inputData = new ArrayList<>();
        inputData.add(Arrays.asList(10.0, 20.0));
        inputData.add(Arrays.asList(-5.0, 0.0, 5.0));
        inputMapper = InputMapper.make(inputData);
        
        // Create OutputMapper
        List<List<Double>> outputData = new ArrayList<>();
        outputData.add(Arrays.asList(1.0, 2.0, 3.0));
        outputData.add(Arrays.asList(-1.0, 0.0, 1.0));
        outputMapper = new OutputMapper(outputData);
        
        // Create SignalAdapter
        adapter = new SignalAdapter(inputMapper, outputMapper);
    }

    @Test
    void testMapInput() {
        // Test mapInput with valid inputs
        List<Double> result1 = adapter.mapInput("aa");
        assertNotNull(result1);
        assertEquals(2, result1.size());
        assertEquals(10.0, result1.get(0));
        assertEquals(-5.0, result1.get(1));
        
        List<Double> result2 = adapter.mapInput("bc");
        assertNotNull(result2);
        assertEquals(2, result2.size());
        assertEquals(20.0, result2.get(0));
        assertEquals(5.0, result2.get(1));
        
        // Test mapInput with null input
        assertNull(adapter.mapInput((String) null));
        
        // Test mapInput with invalid input
        assertNull(adapter.mapInput("xyz"));
    }

    @Test
    void testMapOutput() {
        // Test mapOutput with valid inputs
        List<Double> input1 = Arrays.asList(10.0, 20.0);
        List<Double> output1 = Arrays.asList(1.0, -1.0);
        IOSignalPiece<List<Double>> ioPiece1 = new IOSignalPiece<>(input1, output1);
        String result1 = adapter.mapOutput(ioPiece1);
        assertNotNull(result1);
        assertEquals("aa", result1);
        
        List<Double> input2 = Arrays.asList(20.0, 0.0);
        List<Double> output2 = Arrays.asList(3.0, 1.0);
        IOSignalPiece<List<Double>> ioPiece2 = new IOSignalPiece<>(input2, output2);
        String result2 = adapter.mapOutput(ioPiece2);
        assertNotNull(result2);
        assertEquals("cc", result2);
    }

    @Test
    void testMapInputWord() {
        // Test mapInput with Word<String>
        Word<String> word = Word.fromList(Arrays.asList("aa", "bc"));
        Word<List<Double>> result = adapter.mapInput(word);
        assertNotNull(result);
        assertEquals(2, result.length());
        
        List<Double> firstInput = result.getSymbol(0);
        assertEquals(2, firstInput.size());
        assertEquals(10.0, firstInput.get(0));
        assertEquals(-5.0, firstInput.get(1));
        
        List<Double> secondInput = result.getSymbol(1);
        assertEquals(2, secondInput.size());
        assertEquals(20.0, secondInput.get(0));
        assertEquals(5.0, secondInput.get(1));
    }

    @Test
    void testMapInputs() {
        // Test mapInputs with list of Word<String>
        List<Word<String>> inputs = Arrays.asList(
            Word.fromLetter("aa"),
            Word.fromLetter("bc"),
            null,
            Word.fromList(Arrays.asList("ab", "ba"))
        );
        
        List<Word<List<Double>>> results = adapter.mapInputs(inputs);
        assertNotNull(results);
        assertEquals(4, results.size());
        
        // Check first word
        Word<List<Double>> firstWord = results.get(0);
        assertNotNull(firstWord);
        assertEquals(1, firstWord.length());
        List<Double> firstSymbol = firstWord.getSymbol(0);
        assertEquals(2, firstSymbol.size());
        assertEquals(10.0, firstSymbol.get(0));
        assertEquals(-5.0, firstSymbol.get(1));
        
        // Check second word
        Word<List<Double>> secondWord = results.get(1);
        assertNotNull(secondWord);
        assertEquals(1, secondWord.length());
        List<Double> secondSymbol = secondWord.getSymbol(0);
        assertEquals(2, secondSymbol.size());
        assertEquals(20.0, secondSymbol.get(0));
        assertEquals(5.0, secondSymbol.get(1));
        
        // Check null word
        assertNull(results.get(2));
        
        // Check fourth word
        Word<List<Double>> fourthWord = results.get(3);
        assertNotNull(fourthWord);
        assertEquals(2, fourthWord.length());
        List<Double> fourthFirstSymbol = fourthWord.getSymbol(0);
        assertEquals(2, fourthFirstSymbol.size());
        assertEquals(10.0, fourthFirstSymbol.get(0));
        assertEquals(0.0, fourthFirstSymbol.get(1));
        List<Double> fourthSecondSymbol = fourthWord.getSymbol(1);
        assertEquals(2, fourthSecondSymbol.size());
        assertEquals(20.0, fourthSecondSymbol.get(0));
        assertEquals(-5.0, fourthSecondSymbol.get(1));
    }

    @Test
    void testMapConcrete() {
        // Test mapConcrete
        List<Double> input = Arrays.asList(10.0, 20.0);
        List<Double> output = Arrays.asList(1.0, -1.0);
        IOSignalPiece<List<Double>> ioPiece = new IOSignalPiece<>(input, output);

        List<Double> result = adapter.mapConcrete(ioPiece);
        assertNotNull(result);
        assertEquals(2, result.size());
        assertEquals(output.get(0), result.get(0));
        assertEquals(output.get(1), result.get(1));
    }

    @Test
    void testConstructAbstractAlphabet() {
        // Test constructAbstractAlphabet
        Alphabet<String> alphabet = adapter.constructAbstractAlphabet();
        assertNotNull(alphabet);
        
        // Check that the alphabet contains all possible input combinations
        assertTrue(alphabet.contains("aa"));
        assertTrue(alphabet.contains("ab"));
        assertTrue(alphabet.contains("ac"));
        assertTrue(alphabet.contains("ba"));
        assertTrue(alphabet.contains("bb"));
        assertTrue(alphabet.contains("bc"));
        
        // Check the size of the alphabet
        assertEquals(6, alphabet.size());
    }

    @Test
    void testConstructConcreteAlphabet() {
        // Test constructConcreteAlphabet
        Alphabet<List<Double>> alphabet = adapter.constructConcreteAlphabet();
        assertNotNull(alphabet);
        
        // Check the size of the alphabet
        assertEquals(6, alphabet.size());
        
        // Check that the alphabet contains all possible input combinations
        List<Double> input1 = Arrays.asList(10.0, -5.0);
        List<Double> input2 = Arrays.asList(10.0, 0.0);
        List<Double> input3 = Arrays.asList(10.0, 5.0);
        List<Double> input4 = Arrays.asList(20.0, -5.0);
        List<Double> input5 = Arrays.asList(20.0, 0.0);
        List<Double> input6 = Arrays.asList(20.0, 5.0);
        
        assertTrue(alphabet.containsSymbol(input1));
        assertTrue(alphabet.containsSymbol(input2));
        assertTrue(alphabet.containsSymbol(input3));
        assertTrue(alphabet.containsSymbol(input4));
        assertTrue(alphabet.containsSymbol(input5));
        assertTrue(alphabet.containsSymbol(input6));
    }

    @Test
    void testWithEmptyMappers() {
        // Test with empty InputMapper
        InputMapper emptyInputMapper = InputMapper.make(new ArrayList<>());
        SignalAdapter emptyInputAdapter = new SignalAdapter(emptyInputMapper, outputMapper);
        
        // Test mapInput with empty InputMapper
        assertNull(emptyInputAdapter.mapInput("aa"));
        
        // Test with empty OutputMapper
        OutputMapper emptyOutputMapper = new OutputMapper(new ArrayList<>());
        SignalAdapter emptyOutputAdapter = new SignalAdapter(inputMapper, emptyOutputMapper);
        
        // Test mapOutput with empty OutputMapper
        List<Double> input = Arrays.asList(10.0, 20.0);
        List<Double> output = Arrays.asList(1.0, -1.0);
        IOSignalPiece<List<Double>> ioPiece = new IOSignalPiece<>(input, output);
        String result = emptyOutputAdapter.mapOutput(ioPiece);
        assertEquals("", result);
    }
}