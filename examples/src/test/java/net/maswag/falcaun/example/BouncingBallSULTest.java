package net.maswag.falcaun.example;

import static org.junit.jupiter.api.Assertions.*;

import net.automatalib.word.Word;
import net.maswag.falcaun.IOContinuousSignal;
import net.maswag.falcaun.example.BouncingBall;
import net.maswag.falcaun.example.BouncingBallSUL;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.ExecutionException;

/**
 * Unit tests for the BouncingBallSUL class.
 * These tests verify both the counter functionality and the ObservableSUL implementation.
 */
public class BouncingBallSULTest {

    /**
     * Test that the counter is initially zero.
     */
    @Test
    public void testInitialCounter() {
        try (BouncingBallSUL sul = new BouncingBallSUL()) {
            assertEquals(0, sul.getCounter(), "Counter should be 0 initially");
        }
    }

    /**
     * Test that the counter increments after a complete simulation (pre, step, post).
     */
    @Test
    public void testCounterAfterSimulation() {
        try (BouncingBallSUL sul = new BouncingBallSUL()) {
            // Initial counter should be 0
            assertEquals(0, sul.getCounter(), "Counter should be 0 initially");
            
            // Perform a complete simulation
            sul.pre();
            List<Double> input = new ArrayList<>();
            input.add(2.0); // Wind strength
            sul.step(input);
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
        try (BouncingBallSUL sul = new BouncingBallSUL()) {
            // Initial counter should be 0
            assertEquals(0, sul.getCounter(), "Counter should be 0 initially");
            
            // Perform a complete simulation with multiple steps
            sul.pre();
            List<Double> input = new ArrayList<>();
            input.add(2.0); // Wind strength
            
            // Multiple steps
            sul.step(input);
            sul.step(input);
            sul.step(input);
            
            // Counter should still be 0 before post
            assertEquals(0, sul.getCounter(), "Counter should be 0 before post");
            
            sul.post();
            
            // Counter should be 1 after a complete simulation, regardless of the number of steps
            assertEquals(1, sul.getCounter(), "Counter should be 1 after a complete simulation");
        }
    }

    /**
     * Test that the counter increments after executing a sequence of inputs.
     */
    @Test
    public void testCounterAfterExecute() {
        try (BouncingBallSUL sul = new BouncingBallSUL()) {
            // Initial counter should be 0
            assertEquals(0, sul.getCounter(), "Counter should be 0 initially");
            
            // Simulate execute by doing pre, step, post manually
            sul.pre();
            List<Double> input = new ArrayList<>();
            input.add(2.0); // Wind strength
            sul.step(input);
            sul.post();
            
            // Counter should be 1 after executing a sequence
            assertEquals(1, sul.getCounter(), "Counter should be 1 after executing a sequence");
        }
    }

    /**
     * Test that the counter resets to 0 after calling clear().
     */
    @Test
    public void testCounterClear() {
        try (BouncingBallSUL sul = new BouncingBallSUL()) {
            // Perform a complete simulation
            sul.pre();
            List<Double> input = new ArrayList<>();
            input.add(2.0); // Wind strength
            sul.step(input);
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
        try (BouncingBallSUL sul = new BouncingBallSUL()) {
            // Initial counter should be 0
            assertEquals(0, sul.getCounter(), "Counter should be 0 initially");
            
            // First simulation
            sul.pre();
            List<Double> input = new ArrayList<>();
            input.add(2.0); // Wind strength
            sul.step(input);
            sul.post();
            
            // Counter should be 1 after first simulation
            assertEquals(1, sul.getCounter(), "Counter should be 1 after first simulation");
            
            // Second simulation
            sul.pre();
            sul.step(input);
            sul.post();
            
            // Counter should be 2 after second simulation
            assertEquals(2, sul.getCounter(), "Counter should be 2 after second simulation");
            
            // Third simulation
            sul.pre();
            sul.step(input);
            sul.post();
            
            // If only pre is called, the counter should not increment
            sul.pre();
            
            // Counter should be 3 after third simulation
            assertEquals(3, sul.getCounter(), "Counter should be 3 after third simulation");
        }
    }

    /**
     * Test the execute function
     */
    @Test
    public void testExecute() {
        try (BouncingBallSUL sul = new BouncingBallSUL()) {
            assertEquals(0, sul.getCounter(), "Counter should be 0 initially");

            // Perform a complete simulation
            sul.pre();
            List<List<Double>> input = new ArrayList<>();
            input.add(Collections.singletonList(2.0)); // Wind strength
            input.add(Collections.singletonList(2.0)); // Wind strength
            input.add(Collections.singletonList(2.0)); // Wind strength
            input.add(Collections.singletonList(2.0)); // Wind strength
            IOContinuousSignal<List<Double>> result = sul.execute(Word.fromList(input));

            // Counter should be 1 after executing a sequence
            assertEquals(1, sul.getCounter(), "Counter should be 1 after executing a sequence");
            assertEquals(3.0, result.getContinuousOutputSignal().duration(), 0.0001, "Duration should be 3 seconds");
            result.prefixes(false);
        } catch (ExecutionException | InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Test that the initial state is correctly returned.
     */
    @Test
    public void testInitialState() {
        try (BouncingBallSUL sul = new BouncingBallSUL()) {
            // Initial state should be a default state with zeros
            BouncingBall.SimulationState state = sul.getState();
            assertNotNull(state, "Initial state should not be null");
            assertEquals(0.0, state.time, 0.001, "Initial time should be 0");
            assertEquals(0.0, state.position, 0.001, "Initial position should be 0");
            assertEquals(0.0, state.velocity, 0.001, "Initial velocity should be 0");
        }
    }

    /**
     * Test that the state is updated after a step.
     */
    @Test
    public void testStateAfterStep() {
        try (BouncingBallSUL sul = new BouncingBallSUL()) {
            // Perform a step
            sul.pre();
            List<Double> input = new ArrayList<>();
            input.add(2.0); // Wind strength
            sul.step(input);

            // State should be updated
            BouncingBall.SimulationState state = sul.getState();
            assertNotNull(state, "State should not be null after step");
            assertTrue(state.time == 0, "Time should be 0 after the first step");

            sul.step(input);
            
            // State should be updated
            state = sul.getState();
            assertNotNull(state, "State should not be null after step");
            assertTrue(state.time > 0, "Time should be greater than 0 after step");
            
            // The exact position and velocity will depend on the simulation parameters,
            // but we can check that they're not the default values
            assertNotEquals(0.0, state.position, "Position should be updated after step");
            assertNotEquals(0.0, state.velocity, "Velocity should be updated after step");
        }
    }

    /**
     * Test that the state is reset after pre().
     */
    @Test
    public void testStateReset() {
        try (BouncingBallSUL sul = new BouncingBallSUL()) {
            // Perform a step to change the state
            sul.pre();
            List<Double> input = new ArrayList<>();
            input.add(2.0); // Wind strength
            sul.step(input);
            
            // Verify state has changed
            BouncingBall.SimulationState stateAfterStep = sul.getState();
            assertNotNull(stateAfterStep, "State should not be null after step");
            
            // Reset the state
            sul.pre();
            
            // State should be reset to default
            BouncingBall.SimulationState stateAfterReset = sul.getState();
            assertNotNull(stateAfterReset, "State should not be null after reset");
            
            // After reset, we should have a new default state
            // Note: Since we modified the pre() method to set currentState to null,
            // getState() will return a default state with zeros
            assertEquals(0.0, stateAfterReset.time, 0.001, "Time should be reset to 0");
            assertEquals(0.0, stateAfterReset.position, 0.001, "Position should be reset to 0");
            assertEquals(0.0, stateAfterReset.velocity, 0.001, "Velocity should be reset to 0");
        }
    }

    /**
     * Test that the state is updated correctly after multiple steps.
     */
    @Test
    public void testStateAfterMultipleSteps() {
        try (BouncingBallSUL sul = new BouncingBallSUL()) {
            // Perform multiple steps
            sul.pre();
            List<Double> input = new ArrayList<>();
            input.add(2.0); // Wind strength
            
            // First step
            sul.step(input);
            BouncingBall.SimulationState stateAfterStep1 = sul.getState();
            
            // Second step
            sul.step(input);
            BouncingBall.SimulationState stateAfterStep2 = sul.getState();
            
            // Verify that the state has changed between steps
            assertNotEquals(stateAfterStep1.time, stateAfterStep2.time,
                    "Time should change between steps");
            assertNotEquals(stateAfterStep1.position, stateAfterStep2.position,
                    "Position should change between steps");
            assertNotEquals(stateAfterStep1.velocity, stateAfterStep2.velocity,
                    "Velocity should change between steps");
            
            // Verify that time is increasing
            assertTrue(stateAfterStep2.time > stateAfterStep1.time,
                    "Time should increase with each step");
        }
    }

    /**
     * Test that canFork() returns false for BouncingBallSUL.
     */
    @Test
    public void testCanFork() {
        try (BouncingBallSUL sul = new BouncingBallSUL()) {
            assertFalse(sul.canFork(), "BouncingBallSUL should not support forking");
        }
    }

    /**
     * Test that fork() throws UnsupportedOperationException.
     */
    @Test
    public void testFork() {
        try (BouncingBallSUL sul = new BouncingBallSUL()) {
            assertThrows(UnsupportedOperationException.class, () -> {
                sul.fork();
            }, "fork() should throw UnsupportedOperationException");
        }
    }
}
