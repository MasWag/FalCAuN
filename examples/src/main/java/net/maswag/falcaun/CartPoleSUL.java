package net.maswag.falcaun;

import de.learnlib.sul.ObservableSUL;

/**
 * The {@code CartPoleSUL} class models the cart-pole system as a System Under Learning (SUL).
 * It extends {@code ResetCounterObservableSUL} to provide observable state and reset counting functionality.
 * The cart-pole system simulates a pole balanced on a cart, where the goal is to apply forces
 * to keep the pole upright.
 * <p>
 * This code is a Java migration of the Gymnasium CartPole environment, which is originally from <a href="http://incompleteideas.net/sutton/book/code/pole.c">...</a>
 */
public class CartPoleSUL implements ObservableSUL<CartPoleState, Integer, CartPoleOutput> {
    protected double initX = 0;
    protected double initXDot = 0;
    protected double initTheta = 0;
    protected double initThetaDot = 0;

    // Physical constants for the cart-pole system
    private static final double GRAVITY = 9.8;
    private static final double MASSCART = 1.0;
    private static final double MASSPOLE = 0.1;
    private static final double TOTAL_MASS = MASSCART + MASSPOLE;
    private static final double LENGTH = 0.5;  // Half the pole's length
    private static final double FORCE_MAG = 10.0;
    private static final double TAU = 0.02;    // Time interval between state updates (seconds)
    private static final double THETA_THRESHOLD_RADIANS = 12 * 2 * Math.PI / 360; // Angle threshold
    private static final double X_THRESHOLD = 2.4; // Position threshold

    /**
     * The current state of the cart-pole system
     */
    private CartPoleState state;

    @Override
    public CartPoleState getState() {
        return state;
    }

    public CartPoleSUL() {
        this.state = new CartPoleState(initX, initXDot, initTheta, initThetaDot);
    }

    public CartPoleSUL(double x, double xDot, double theta, double thetaDot) {
        this.initX = x;
        this.initXDot = xDot;
        this.initTheta = theta;
        this.initThetaDot = thetaDot;

        this.state = new CartPoleState(x, xDot, theta, thetaDot);
    }


    /**
     * Prepares the SUL for a new interaction sequence.
     * Resets the system to the initial state.
     */
    @Override
    public void pre() {
        this.state = new CartPoleState(initX, initXDot, initTheta, initThetaDot);
    }

    /**
     * Performs any necessary cleanup after an interaction sequence.
     */
    @Override
    public void post() {
        // Any cleanup after each step, if needed
    }

    /**
     * Applies the given action to the cart-pole system and updates its state.
     *
     * @param action the action to apply (0 for left force, 1 for right force)
     * @return the output containing the new state and a flag indicating if the episode is done
     */
    @Override
    public CartPoleOutput step(Integer action) {
        double force = (action == 1 ? FORCE_MAG : -FORCE_MAG);
        double cosTheta = Math.cos(state.getTheta());
        double sinTheta = Math.sin(state.getTheta());

        double temp = (force + MASSPOLE * LENGTH * state.getThetaDot() * state.getThetaDot() * sinTheta) / TOTAL_MASS;
        double thetaAcc = (GRAVITY * sinTheta - cosTheta * temp) /
                (LENGTH * (4.0 / 3.0 - MASSPOLE * cosTheta * cosTheta / TOTAL_MASS));
        double xAcc = temp - MASSPOLE * LENGTH * thetaAcc * cosTheta / TOTAL_MASS;

        // Update the state variables using Euler's method
        state.setX(state.getX() + TAU * state.getXDot());
        state.setXDot(state.getXDot() + TAU * xAcc);
        state.setTheta(state.getTheta() + TAU * state.getThetaDot());
        state.setThetaDot(state.getThetaDot() + TAU * thetaAcc);

        // Check if the state is within thresholds to determine if it's "done"
        boolean done = Math.abs(state.getX()) > X_THRESHOLD || Math.abs(state.getTheta()) > THETA_THRESHOLD_RADIANS;
        return new CartPoleOutput(state, done);
    }

    /**
     * Indicates whether this SUL supports forking.
     *
     * @return {@code true} if forking is supported; {@code false} otherwise
     */
    @Override
    public boolean canFork() {
        return true; // This SUL supports forking
    }

    /**
     * Creates a fork of this SUL, which is a new instance with the same initial state.
     *
     * @return a new {@code CartPoleSUL} instance
     */
    @Override
    public ObservableSUL<CartPoleState, Integer, CartPoleOutput> fork() {
        return new CartPoleSUL();
    }
}