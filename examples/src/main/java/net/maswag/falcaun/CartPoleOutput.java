package net.maswag.falcaun;

import lombok.AllArgsConstructor;
import lombok.Data;

/**
 * Represents the output of the cart-pole system after an action is applied.
 */
@Data
@AllArgsConstructor
public class CartPoleOutput {
    /**
     * The current state of the cart-pole system
     */
    private CartPoleState state;

    /**
     * Flag indicating whether the episode has ended
     */
    private boolean done;
}