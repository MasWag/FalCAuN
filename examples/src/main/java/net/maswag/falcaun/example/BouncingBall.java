package net.maswag.falcaun.example;

import lombok.Getter;

import java.util.ArrayList;
import java.util.List;

public class BouncingBall {

    // Default constants
    public static final double DEFAULT_INITIAL_POSITION = 50.0; // in meters
    public static final double DEFAULT_INITIAL_VELOCITY = 0.0;    // in m/s
    public static final double DEFAULT_SIMULATION_STEP = 0.0001;    // in seconds
    public static final double DEFAULT_BOUNCE_COEFFICIENT = 0.9;  // energy loss factor at bounce
    public static final double DEFAULT_GRAVITY = 9.81;            // gravitational acceleration in m/s^2
    public static final double DEFAULT_WIND_STRENGTH = 2.0;         // upward acceleration from wind in m/s^2

    // Initial configuration parameters
    private double initialPosition;
    private double initialVelocity;
    private double simulationStep;
    private double bounceCoefficient;
    private double gravity;

    // Simulation state variables
    @Getter
    private double position;
    @Getter
    private double velocity;
    private double elapsedTime;

    /**
     * Inner class representing a simulation state tuple: (time, position, velocity)
     */
    public static class SimulationState {
        public final double time;
        public final double position;
        public final double velocity;

        public SimulationState(double time, double position, double velocity) {
            this.time = time;
            this.position = position;
            this.velocity = velocity;
        }

        @Override
        public String toString() {
            return String.format("Time: %.2f s, Position: %.2f m, Velocity: %.2f m/s",
                    time, position, velocity);
        }
    }

    /**
     * Constructor that takes all parameters.
     *
     * @param initialPosition   the starting position (meters)
     * @param initialVelocity   the starting velocity (m/s)
     * @param simulationStep    the time step for the simulation (s)
     * @param bounceCoefficient the energy loss factor when bouncing
     * @param gravity           gravitational acceleration (m/s^2)
     */
    public BouncingBall(double initialPosition, double initialVelocity, double simulationStep,
                        double bounceCoefficient, double gravity) {
        this.initialPosition = initialPosition;
        this.initialVelocity = initialVelocity;
        this.simulationStep = simulationStep;
        this.bounceCoefficient = bounceCoefficient;
        this.gravity = gravity;
        reset();
    }

    /**
     * Constructor that uses default values for parameters not provided.
     * Only initial position and simulation step are provided.
     *
     * @param initialPosition the starting position (meters)
     * @param simulationStep  the time step for the simulation (s)
     */
    public BouncingBall(double initialPosition, double simulationStep) {
        this(initialPosition, DEFAULT_INITIAL_VELOCITY, simulationStep, DEFAULT_BOUNCE_COEFFICIENT, DEFAULT_GRAVITY);
    }

    /**
     * Resets the simulation state to the initial conditions.
     */
    public void reset() {
        this.position = initialPosition;
        this.velocity = initialVelocity;
        this.elapsedTime = 0.0;
    }

    /**
     * Simulates the perturbed bouncing ball for a given duration with a constant wind strength
     * and returns the state at each simulation step as a list of tuples.
     *
     * The wind provides an additional upward acceleration.
     *
     * @param duration    the total time over which to run the simulation (s)
     * @param windStrength the upward acceleration due to the wind (m/s^2)
     * @return a list of simulation states (time, position, velocity) at each time step
     */
    public List<SimulationState> step(double duration, double windStrength) {
        List<SimulationState> states = new ArrayList<>();
        double timePassed = 0.0;
        // Record the initial state.
        states.add(new SimulationState(elapsedTime, position, velocity));
        double initialTime = elapsedTime;

        while (timePassed < duration) {
            // Use the smaller of the simulation step or the remaining time.
            double dt = Math.min(simulationStep, duration - timePassed);

            // Update velocity: wind provides upward acceleration and gravity pulls downward.
            velocity += (windStrength - gravity) * dt;

            // Update position using the current velocity.
            position += velocity * dt;

            // Bounce: if the ball goes below ground level, set position to ground and reverse velocity with damping.
            if (position < 0) {
                position = 0;
                velocity = -velocity * bounceCoefficient;
            }

            timePassed += dt;
            elapsedTime += dt;
            // Adjust elapsed time to ensure it doesn't exceed the total duration.
            if (timePassed >= duration) {
                elapsedTime = initialTime + duration;
            }

            // Record the state after this simulation step.
            states.add(new SimulationState(elapsedTime, position, velocity));
        }
        return states;
    }

    /**
     * Main method for command-line testing of the perturbed bouncing ball simulation.
     * Accepts up to three optional arguments: initial position, simulation step, and wind strength.
     *
     * When no wind strength is provided, the default wind strength is used.
     */
    public static void main(String[] args) {
        BouncingBall ball;
        double windStrength = DEFAULT_WIND_STRENGTH;

        if (args.length >= 2) {
            try {
                double initialPosition = Double.parseDouble(args[0]);
                double simulationStep = Double.parseDouble(args[1]);
                ball = new BouncingBall(initialPosition, simulationStep);
                if (args.length >= 3) {
                    windStrength = Double.parseDouble(args[2]);
                }
            } catch (NumberFormatException e) {
                System.out.println("Invalid arguments. Using default values.");
                ball = new BouncingBall(DEFAULT_INITIAL_POSITION, DEFAULT_SIMULATION_STEP);
            }
        } else {
            // Use default values if parameters are not provided.
            ball = new BouncingBall(DEFAULT_INITIAL_POSITION, DEFAULT_SIMULATION_STEP);
        }

        // Reset simulation to start from the initial state.
        ball.reset();

        // Simulate for a total of 10 seconds with the specified wind strength.
        double simulationDuration = 10.0; // seconds
        List<SimulationState> simulationStates = ball.step(simulationDuration, windStrength);

        // Print all the simulation states.
        System.out.println("Simulation states with wind strength " + windStrength + " m/s^2:");
        for (SimulationState state : simulationStates) {
            System.out.println(state);
        }
    }
}

