package net.maswag.falcaun;

import lombok.AllArgsConstructor;
import lombok.Getter;

/**
 * Represents a pair of input and output signals at one time step in a system's behavior.
 *
 * This class encapsulates an input signal and its corresponding output signal for a single time step.
 * It is used to store and manage the input-output pairs during simulations, verifications, and other analyses of system behavior.
 *
 * @param <I> The type of the input and output signals.
 */
@Getter
@AllArgsConstructor
public class IOSignalPiece<I> {
    /**
     * The input signal at this time step.
     */
    final private I inputSignal;

    /**
     * The output signal at this time step.
     */
    final private I outputSignal;
}
