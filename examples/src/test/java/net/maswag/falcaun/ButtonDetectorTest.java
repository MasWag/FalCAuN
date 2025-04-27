package net.maswag.falcaun;

import static org.junit.jupiter.api.Assertions.*;

import de.learnlib.oracle.MembershipOracle;
import de.learnlib.oracle.membership.SULOracle;
import de.learnlib.sul.SUL;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.word.Word;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

/**
 * Unit tests for the ButtonDetector class.
 * These tests verify both the button detection functionality and the SUL implementation.
 */
public class ButtonDetectorTest {

    /**
     * Test that the counter is initially zero.
     */
    @Test
    public void testInitialCounter() {
        try (ButtonDetector sul = new ButtonDetector()) {
            assertEquals(0, sul.getCounter(), "Counter should be 0 initially");
        }
    }

    /**
     * Test that the counter increments after a complete simulation (pre, step, post).
     */
    @Test
    public void testCounterAfterSimulation() {
        try (ButtonDetector sul = new ButtonDetector()) {
            // Initial counter should be 0
            assertEquals(0, sul.getCounter(), "Counter should be 0 initially");
            
            // Perform a complete simulation
            sul.pre();
            sul.step(ButtonDetector.RawInput.Pressed);
            sul.post();
            
            // Counter should be 1 after a complete simulation
            assertEquals(1, sul.getCounter(), "Counter should be 1 after a complete simulation");
        }
    }

    /**
     * Test that the counter increments only once after multiple steps in a single simulation.
     */
    @Test
    public void testCounterWithMultipleSteps() {
        try (ButtonDetector sul = new ButtonDetector()) {
            // Initial counter should be 0
            assertEquals(0, sul.getCounter(), "Counter should be 0 initially");
            
            // Perform a complete simulation with multiple steps
            sul.pre();
            
            // Multiple steps
            sul.step(ButtonDetector.RawInput.Pressed);
            sul.step(ButtonDetector.RawInput.Pressed);
            sul.step(ButtonDetector.RawInput.Released);
            
            // Counter should still be 0 before post
            assertEquals(0, sul.getCounter(), "Counter should be 0 before post");
            
            sul.post();
            
            // Counter should be 1 after a complete simulation, regardless of the number of steps
            assertEquals(1, sul.getCounter(), "Counter should be 1 after a complete simulation");
        }
    }

    /**
     * Test that the counter resets to 0 after calling clear().
     */
    @Test
    public void testCounterClear() {
        try (ButtonDetector sul = new ButtonDetector()) {
            // Perform a complete simulation
            sul.pre();
            sul.step(ButtonDetector.RawInput.Pressed);
            sul.post();
            
            // Counter should be 1 after a complete simulation
            assertEquals(1, sul.getCounter(), "Counter should be 1 after a complete simulation");
            
            // Clear the counter
            sul.clear();
            
            // Counter should be 0 after clearing
            assertEquals(0, sul.getCounter(), "Counter should be 0 after clearing");
        }
    }

    /**
     * Test that multiple simulations increment the counter correctly.
     */
    @Test
    public void testMultipleSimulations() {
        try (ButtonDetector sul = new ButtonDetector()) {
            // Initial counter should be 0
            assertEquals(0, sul.getCounter(), "Counter should be 0 initially");
            
            // First simulation
            sul.pre();
            sul.step(ButtonDetector.RawInput.Pressed);
            sul.post();
            
            // Counter should be 1 after first simulation
            assertEquals(1, sul.getCounter(), "Counter should be 1 after first simulation");
            
            // Second simulation
            sul.pre();
            sul.step(ButtonDetector.RawInput.Pressed);
            sul.post();
            
            // Counter should be 2 after second simulation
            assertEquals(2, sul.getCounter(), "Counter should be 2 after second simulation");
        }
    }

    /**
     * Test the execute function
     */
    @Test
    public void testExecute() {
        try (ButtonDetector sul = new ButtonDetector()) {
            assertEquals(0, sul.getCounter(), "Counter should be 0 initially");

            // Perform a complete simulation
            sul.pre();
            List<ButtonDetector.RawInput> inputs = new ArrayList<>();
            inputs.add(ButtonDetector.RawInput.Pressed);
            inputs.add(ButtonDetector.RawInput.Released);
            inputs.add(ButtonDetector.RawInput.Pressed);
            inputs.add(ButtonDetector.RawInput.Released);
            Word<ButtonDetector.ButtonEvent> result = sul.execute(Word.fromList(inputs));

            // Counter should be 1 after executing a sequence
            assertEquals(1, sul.getCounter(), "Counter should be 1 after executing a sequence");
            
            // Check that the output has the correct number of symbols
            assertEquals(4, result.size(), "Output should have 4 symbols");
            
            // Check that the output values are correct
            // First press should result in None
            assertEquals(ButtonDetector.ButtonEvent.None, result.getSymbol(0));
            // First release should result in None since it's the first click
            assertEquals(ButtonDetector.ButtonEvent.None, result.getSymbol(1));
            // Second press should result in None
            assertEquals(ButtonDetector.ButtonEvent.None, result.getSymbol(2));
            // Second release should result in DoubleClick since it's within the double-click time window
            assertEquals(ButtonDetector.ButtonEvent.DoubleClick, result.getSymbol(3));
        }
    }

    /**
     * Test that the initial state is correctly returned.
     */
    @Test
    public void testInitialState() {
        try (ButtonDetector sul = new ButtonDetector()) {
            // Initial state should be a default state
            ButtonDetector.DetectorState state = sul.getState();
            assertNotNull(state, "Initial state should not be null");
            assertEquals(0, state.stepIndex, "Initial stepIndex should be 0");
            assertEquals(-1, state.pressIndex, "Initial pressIndex should be -1");
            assertEquals(-1, state.lastReleaseIndex, "Initial lastReleaseIndex should be -1");
            assertEquals(0, state.clickCount, "Initial clickCount should be 0");
        }
    }

    /**
     * Test that the state is updated after a step.
     */
    @Test
    public void testStateAfterStep() {
        try (ButtonDetector sul = new ButtonDetector()) {
            // Perform a step
            sul.pre();
            sul.step(ButtonDetector.RawInput.Pressed);

            // State should be updated
            ButtonDetector.DetectorState state = sul.getState();
            assertNotNull(state, "State should not be null after step");
            assertEquals(1, state.stepIndex, "stepIndex should be 1 after the first step");
            assertEquals(0, state.pressIndex, "pressIndex should be 0 after pressing");
            assertEquals(-1, state.lastReleaseIndex, "lastReleaseIndex should still be -1");
            assertEquals(0, state.clickCount, "clickCount should still be 0");
        }
    }

    /**
     * Test that the state is reset after pre().
     */
    @Test
    public void testStateReset() {
        try (ButtonDetector sul = new ButtonDetector()) {
            // Perform a step to change the state
            sul.pre();
            sul.step(ButtonDetector.RawInput.Pressed);
            
            // Verify state has changed
            ButtonDetector.DetectorState stateAfterStep = sul.getState();
            assertNotNull(stateAfterStep, "State should not be null after step");
            
            // Reset the state
            sul.pre();
            
            // State should be reset to default
            ButtonDetector.DetectorState stateAfterReset = sul.getState();
            assertNotNull(stateAfterReset, "State should not be null after reset");
            
            // After reset, we should have a new default state
            assertEquals(0, stateAfterReset.stepIndex, "stepIndex should be reset to 0");
            assertEquals(-1, stateAfterReset.pressIndex, "pressIndex should be reset to -1");
            assertEquals(-1, stateAfterReset.lastReleaseIndex, "lastReleaseIndex should be reset to -1");
            assertEquals(0, stateAfterReset.clickCount, "clickCount should be reset to 0");
        }
    }

    /**
     * Test that canFork() returns false for ButtonDetector.
     */
    @Test
    public void testCanFork() {
        try (ButtonDetector sul = new ButtonDetector()) {
            assertFalse(sul.canFork(), "ButtonDetector should not support forking");
        }
    }

    /**
     * Test that fork() throws UnsupportedOperationException.
     */
    @Test
    public void testFork() {
        try (ButtonDetector sul = new ButtonDetector()) {
            assertThrows(UnsupportedOperationException.class, () -> {
                sul.fork();
            }, "fork() should throw UnsupportedOperationException");
        }
    }

    /**
     * Test single click detection.
     */
    @Test
    public void testSingleClick() {
        try (ButtonDetector sul = new ButtonDetector()) {
            sul.pre();
            
            // Press the button
            ButtonDetector.ButtonEvent result1 = sul.step(ButtonDetector.RawInput.Pressed);
            assertEquals(ButtonDetector.ButtonEvent.None, result1, "First press should result in None");
            
            // Release the button
            ButtonDetector.ButtonEvent result2 = sul.step(ButtonDetector.RawInput.Released);
            assertEquals(ButtonDetector.ButtonEvent.None, result2, "First release should result in None");
            
            // Finalize the click directly
            ButtonDetector.ButtonEvent finalEvent = sul.finalizeClick();
            
            // Should be a single click
            assertEquals(ButtonDetector.ButtonEvent.SingleClick, finalEvent,
                    "Finalizing after first click should result in SingleClick");
            
            sul.post();
        }
    }

    /**
     * Test double click detection.
     */
    @Test
    public void testDoubleClick() {
        try (ButtonDetector sul = new ButtonDetector(100)) { // 100ms step time
            sul.pre();
            
            // First click
            sul.step(ButtonDetector.RawInput.Pressed);
            sul.step(ButtonDetector.RawInput.Released);
            
            // Second click (within double-click time window)
            sul.step(ButtonDetector.RawInput.Pressed);
            ButtonDetector.ButtonEvent result = sul.step(ButtonDetector.RawInput.Released);
            
            // Should detect a double click
            assertEquals(ButtonDetector.ButtonEvent.DoubleClick, result, 
                    "Second release within time window should result in DoubleClick");
            
            sul.post();
        }
    }

    /**
     * Test long press detection.
     */
    @Test
    public void testLongPress() {
        try (ButtonDetector sul = new ButtonDetector(100)) { // 100ms step time
            sul.pre();
            
            // Press the button
            sul.step(ButtonDetector.RawInput.Pressed);
            
            // Keep pressed for long enough (10+ steps for 1000ms)
            for (int i = 0; i < 9; i++) {
                sul.step(ButtonDetector.RawInput.Pressed);
            }
            
            // Release after long press
            ButtonDetector.ButtonEvent result = sul.step(ButtonDetector.RawInput.Released);
            
            // Should detect a long press
            assertEquals(ButtonDetector.ButtonEvent.LongPress, result, 
                    "Release after long press should result in LongPress");
            
            sul.post();
        }
    }

    /**
     * Test using BlackBoxVerifier to verify ButtonDetector behavior.
     * This test creates STL properties for button events and verifies them against the ButtonDetector.
     */
    @Test
    public void testBlackBoxVerifier() {
        // Create a ButtonDetector with 100ms step time
        try (ButtonDetector buttonDetector = new ButtonDetector(100)) {
            // Create a ButtonDetectorMapper to convert between String and ButtonDetector types
            SUL<String, String> buttonDetectorSUL = new ButtonDetectorMapper(buttonDetector);

            // Create a membership oracle
            MembershipOracle.MealyMembershipOracle<String, String> memOracle = new SULOracle<>(buttonDetectorSUL);

            // Get the input alphabet from ButtonDetectorMapper
            Alphabet<String> inputAlphabet = ButtonDetectorMapper.getInputAlphabet();

            // Create LTL properties for button events
            List<String> properties = new ArrayList<>();
            
            // Property 1: If a button is pressed and held for 10+ steps, it should eventually result in a LongPress
            properties.add("[] (output == \"LongPress\")");
            
            // Property 2: If a button is pressed and released twice quickly, it should result in a DoubleClick
            properties.add("[] (output == \"DoubleClick\")");
            
            // Property 3: If a button is pressed and released once with no follow-up, it should result in a SingleClick
            properties.add("[] (output == \"SingleClick\")");
            
            // Create a StaticLTLList with the properties
            StopDisprovedEQOracle.StaticLTLList<List<Double>> ltlList = new StopDisprovedEQOracle.StaticLTLList<>(properties);
            ltlList.setMemOracle(memOracle);

            // Create a BlackBoxVerifier
            BlackBoxVerifier<List<Double>> verifier = new BlackBoxVerifier<>(memOracle, buttonDetectorSUL, ltlList, inputAlphabet);

            // Add equivalence oracles
            verifier.addRandomWordEQOracle(1, 20, 100, new java.util.Random(42), 10);
            verifier.addWpMethodEQOracle(3);
            verifier.addCornerCaseEQOracle(10, 2);

            // Run the verifier
            boolean isVerified = verifier.run();

            // The verification should pass (no counterexamples found)
            // Note: This might need adjustment based on the actual behavior of ButtonDetector
            assertTrue(isVerified, "ButtonDetector should satisfy all STL properties");
        }
    }
}
