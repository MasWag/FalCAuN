package net.maswag.falcaun;

import de.learnlib.exception.SULException;
import de.learnlib.sul.ObservableSUL;
import lombok.Getter;
import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;
import org.jetbrains.annotations.NotNull;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutionException;

/**
 * System Under Learning implementation for the BouncingBall model.
 * This class wraps the BouncingBall simulation model to conform to the ContinuousNumericSUL interface.
 */
public class BouncingBallSUL implements ContinuousNumericSUL, ObservableSUL<BouncingBall.SimulationState, List<Double>, IOSignalPiece<List<Double>>> {
    private final BouncingBall model;
    @Getter
    private int counter;
    @Getter
    private double simulationTimeSecond;
    private final double signalStep;
    private double lastStepTime;
    private BouncingBall.SimulationState currentState;
    public static final double DEFAULT_SIMULATION_STEP = 1.0;    // in seconds

    /**
     * Constructor with default parameters.
     */
    public BouncingBallSUL() {
        this(BouncingBall.DEFAULT_INITIAL_POSITION, DEFAULT_SIMULATION_STEP, BouncingBall.DEFAULT_SIMULATION_STEP);
    }

    /**
     * Constructor with custom initial position and simulation step.
     *
     * @param initialPosition the starting position of the ball (meters)
     * @param simulationStep  the time step for the simulation (seconds)
     */
    public BouncingBallSUL(double initialPosition, double signalStep, double simulationStep) {
        this.model = new BouncingBall(initialPosition, simulationStep);
        this.counter = 0;
        this.simulationTimeSecond = 0.0;
        this.signalStep = signalStep;
        this.lastStepTime = 0.0;
    }

    /**
     * Constructor with all custom parameters.
     *
     * @param initialPosition   the starting position of the ball (meters)
     * @param initialVelocity   the starting velocity of the ball (m/s)
     * @param simulationStep    the time step for the simulation (seconds)
     * @param bounceCoefficient the energy loss factor when bouncing
     * @param gravity           gravitational acceleration (m/s^2)
     */
    public BouncingBallSUL(double initialPosition, double initialVelocity, double simulationStep,
                           double bounceCoefficient, double gravity) {
        this.model = new BouncingBall(initialPosition, initialVelocity, simulationStep, bounceCoefficient, gravity);
        this.counter = 0;
        this.simulationTimeSecond = 0.0;
        this.signalStep = simulationStep;
        this.lastStepTime = 0.0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean canFork() {
        return false;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void pre() {
        model.reset();
        lastStepTime = 0.0;
        // Initialize with default values - will be updated on first step
        currentState = null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void post() {
        // Increment counter after a complete simulation
        counter++;
    }

    /**
     * Execute the SUL by feeding single step input.
     * The input signal is expected to be a list with a single element representing the wind strength.
     *
     * @param inputSignal the input signal at one time step (wind strength)
     * @return the output signal at one time step with the previous output signals
     */
    @Nullable
    @Override
    public ExtendedIOSignalPiece<List<Double>> step(@Nullable List<Double> inputSignal) throws SULException {
        if (inputSignal == null || inputSignal.isEmpty()) {
            return null;
        }

        long startTime = System.nanoTime();
        
        // Extract wind strength from input signal (first element)
        double windStrength = inputSignal.get(0);
        
        // Simulate the bouncing ball for one signal step
        List<BouncingBall.SimulationState> states = model.step(signalStep, windStrength);
        
        // Update current state to the last state in the simulation
        if (!states.isEmpty()) {
            currentState = states.get(states.size() - 1);
        }
        
        // Create a list of output signals (position and velocity)
        ValueWithTime<List<Double>> valueWithTime = asListValueWithTime(states);

        // Update time counter
        long endTime = System.nanoTime();
        simulationTimeSecond += (endTime - startTime) / 1e9;
        
        double currentTime = lastStepTime + signalStep;
        ExtendedIOSignalPiece<List<Double>> result = new ExtendedIOSignalPiece<>(
                inputSignal, valueWithTime, lastStepTime, currentTime);
        
        lastStepTime = currentTime;
        
        return result;
    }

    private static @NotNull ValueWithTime<List<Double>> asListValueWithTime(List<BouncingBall.SimulationState> states) {
        List<List<Double>> outputSignals = new ArrayList<>();
        for (BouncingBall.SimulationState state : states) {
            List<Double> output = new ArrayList<>();
            output.add(state.position);
            output.add(state.velocity);
            outputSignals.add(output);
        }

        // Create a ValueWithTime object from the simulation states
        List<Double> timestamps = new ArrayList<>();
        for (BouncingBall.SimulationState state : states) {
            timestamps.add(state.time);
        }
        return new ValueWithTime<>(timestamps, outputSignals);
    }

    /**
     * Execute the SUL by feeding the entire input signal.
     *
     * @param inputSignal the sequence of input signals
     * @return the continuous output signal
     */
    @Override
    public IOContinuousSignal<List<Double>> execute(Word<List<Double>> inputSignal) throws InterruptedException, ExecutionException {
        if (inputSignal.isEmpty()) {
            return new IOContinuousSignal<>(inputSignal, Word.epsilon(), new ValueWithTime<>(), signalStep);
        }

        long startTime = System.nanoTime();
        
        // Reset the model before execution
        pre();
        
        // Lists to store timestamps and output values
        List<Double> timestamps = new ArrayList<>();
        List<List<Double>> outputValues = new ArrayList<>();
        WordBuilder<List<Double>> outputBuilder = new WordBuilder<>();
        
        // Process each input signal
        for (int i = 0; i < inputSignal.size(); i++) {
            List<Double> input = inputSignal.getSymbol(i);
            double windStrength = input.get(0);
            
            // Simulate for one signal step
            List<BouncingBall.SimulationState> states = model.step(signalStep, windStrength);
            
            // Update current state to the last state in the simulation
            if (!states.isEmpty()) {
                currentState = states.get(states.size() - 1);
            }
            
            // Extract the last state as the output for this step
            BouncingBall.SimulationState lastState = states.get(states.size() - 1);
            List<Double> output = new ArrayList<>();
            output.add(lastState.position);
            output.add(lastState.velocity);
            outputBuilder.add(output);
            
            // Add all intermediate states to the continuous signal
            for (BouncingBall.SimulationState state : states) {
                timestamps.add(state.time);
                List<Double> stateOutput = new ArrayList<>();
                stateOutput.add(state.position);
                stateOutput.add(state.velocity);
                outputValues.add(stateOutput);
            }
            
        }
        
        // Create the ValueWithTime object for the continuous signal
        ValueWithTime<List<Double>> valueWithTime = new ValueWithTime<>(timestamps, outputValues);
        // Update simulation time
        long endTime = System.nanoTime();
        simulationTimeSecond += (endTime - startTime) / 1e9;
        
        
        // Reset the model after execution
        post();
        
        return new IOContinuousSignal<>(inputSignal, outputBuilder.toWord(), valueWithTime, signalStep);
    }

    /**
     * {@inheritDoc}
     */
    @Nonnull
    @Override
    public ObservableSUL<BouncingBall.SimulationState, List<Double>, IOSignalPiece<List<Double>>> fork() throws UnsupportedOperationException {
        throw new UnsupportedOperationException("BouncingBallSUL does not support forking");
    }
    
    /**
     * {@inheritDoc}
     * Returns the current state of the bouncing ball simulation.
     *
     * @return the current simulation state
     */
    @Override
    public BouncingBall.SimulationState getState() {
        // If currentState is null (before first step), return a default state
        if (currentState == null) {
            return new BouncingBall.SimulationState(0.0, 0.0, 0.0);
        }
        return currentState;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void clear() {
        counter = 0;
        simulationTimeSecond = 0.0;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void close() {
        // No resources to close
    }
}
