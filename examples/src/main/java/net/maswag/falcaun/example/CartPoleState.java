package net.maswag.falcaun.example;

import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * Represents the state of the cart-pole system.
 */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class CartPoleState {
    /**
     * Cart position
     */
    private double x;

    /**
     * Cart velocity
     */
    private double xDot;

    /**
     * Pole angle in radians
     */
    private double theta;

    /**
     * Pole angular velocity
     */
    private double thetaDot;
}
