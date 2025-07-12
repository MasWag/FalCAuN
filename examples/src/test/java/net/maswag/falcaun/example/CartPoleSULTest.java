package net.maswag.falcaun.example;

import static org.junit.jupiter.api.Assertions.*;

import com.pholser.junit.quickcheck.Property;
import com.pholser.junit.quickcheck.generator.InRange;
import com.pholser.junit.quickcheck.runner.JUnitQuickcheck;

import net.maswag.falcaun.example.CartPoleOutput;
import net.maswag.falcaun.example.CartPoleSUL;
import net.maswag.falcaun.example.CartPoleState;

import org.junit.runner.RunWith;

import static org.junit.jupiter.api.Assertions.*;

@RunWith(JUnitQuickcheck.class)
public class CartPoleSULTest {

    @Property
    public void testInitialState(@InRange(min = "-0.5", max = "0.5") double initX, @InRange(min = "-0.5", max = "0.5") double initXDot,
                                 @InRange(min = "-0.5", max = "0.5") double initTheta, @InRange(min = "-0.5", max = "0.5") double initThetaDot) {
        CartPoleSUL cartPoleSUL = new CartPoleSUL(initX, initXDot, initTheta, initThetaDot);

        CartPoleState initialState = cartPoleSUL.getState();
        assertEquals(initX, initialState.getX(), 1e-5, "Initial x should be 0");
        assertEquals(initXDot, initialState.getXDot(), 1e-5, "Initial xDot should be 0");
        assertEquals(initTheta, initialState.getTheta(), 1e-5, "Initial theta should be 0");
        assertEquals(initThetaDot, initialState.getThetaDot(), 1e-5, "Initial thetaDot should be 0");
    }

    @Property
    public void testActionRight(@InRange(min = "-0.5", max = "0.5") double initX, @InRange(min = "-0.5", max = "0.5") double initXDot,
                                @InRange(min = "-0.5", max = "0.5") double initTheta, @InRange(min = "-0.5", max = "0.5") double initThetaDot) {
        CartPoleSUL cartPoleSUL = new CartPoleSUL(initX, initXDot, initTheta, initThetaDot);

        cartPoleSUL.step(1); // Apply right force
        CartPoleOutput output = cartPoleSUL.step(1); // Apply right force

        CartPoleState state = output.getState();
        assertNotEquals(initX, state.getX(), "x should have changed after step");
        assertNotEquals(initXDot, state.getXDot(), "xDot should have changed after step");
        assertNotEquals(initTheta, state.getTheta(), "theta should have changed after step");
        assertNotEquals(initThetaDot, state.getThetaDot(), "thetaDot should have changed after step");
    }

    @Property
    public void testActionLeft(@InRange(min = "-0.5", max = "0.5") double initX, @InRange(min = "-0.5", max = "0.5") double initXDot,
                               @InRange(min = "-0.5", max = "0.5") double initTheta, @InRange(min = "-0.5", max = "0.5") double initThetaDot) {
        CartPoleSUL cartPoleSUL = new CartPoleSUL(initX, initXDot, initTheta, initThetaDot);

        cartPoleSUL.step(0); // Apply left force
        CartPoleOutput output = cartPoleSUL.step(0); // Apply left force

        CartPoleState state = output.getState();
        assertNotEquals(initX, state.getX(), "x should have changed after step");
        assertNotEquals(initXDot, state.getXDot(), "xDot should have changed after step");
        assertNotEquals(initTheta, state.getTheta(), "theta should have changed after step");
        assertNotEquals(initThetaDot, state.getThetaDot(), "thetaDot should have changed after step");
    }

    @Property
    public void testMultipleSteps(@InRange(min = "-0.5", max = "0.5") double initX, @InRange(min = "-0.5", max = "0.5") double initXDot,
                                  @InRange(min = "-0.5", max = "0.5") double initTheta, @InRange(min = "-0.5", max = "0.5") double initThetaDot) {
        CartPoleSUL cartPoleSUL = new CartPoleSUL(initX, initXDot, initTheta, initThetaDot);

        // Define a sequence of actions and apply them
        int[] actions = {1, 0, 1, 1, 0}; // Right, Left, Right, Right, Left
        boolean done = false;
        for (int action : actions) {
            CartPoleOutput output = cartPoleSUL.step(action);
            done = output.isDone();
            if (done) break;
        }

        // Validate that the environment is still running or terminated based on steps
        if (!done) {
            assertFalse(done, "The environment should not be done after limited steps.");
        } else {
            assertTrue(done, "The environment terminated early, check thresholds or initial states.");
        }
    }
}
