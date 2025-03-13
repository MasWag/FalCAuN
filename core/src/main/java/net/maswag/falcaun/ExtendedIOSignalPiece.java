package net.maswag.falcaun;


import lombok.Getter;

import java.util.List;

/**
 * A pair of input and output signals at one time step potentially with some previous output signals.
 *
 * <p>This class is used for continuous-time systems with discrete sampling. </p>
 *
 * @param <I> the type of the input and output signals
 */
@Getter
public class ExtendedIOSignalPiece<I> extends IOSignalPiece<I> {
    /**
     * The previous output signals. This must not include the previous step and must include the current step
     */
    protected List<I> previousOutputSignals;

    /**
     * Constructor for the signal pieces.
     *
     * @param inputSignal the current step of the input signal
     * @param outputSignal the current step of the output signal
     * @param previousOutputSignals the output signals between the previous step and the current step
     *                              excluding the previous step and including the current step
     * @throws IllegalArgumentException if the current output signal is not the last element of previousOutputSignals
     */
    public ExtendedIOSignalPiece(I inputSignal, I outputSignal, List<I> previousOutputSignals) {
        super(inputSignal, outputSignal);
        if (outputSignal == null) {
            throw new IllegalArgumentException("The output signal must not be null");
        }
        if (previousOutputSignals == null) {
            throw new IllegalArgumentException("The previous output signals must not be null");
        }
        // The following equality must be based on the elements, not the references.
        if (!outputSignal.equals(previousOutputSignals.get(previousOutputSignals.size() - 1))) {
            throw new IllegalArgumentException("The current output signal must be the last element of previousOutputSignals");
        }
        this.previousOutputSignals = previousOutputSignals;
    }

    /**
     * Constructor for the first signal piece.
     *
     * @param inputStep the current step of the input signal
     * @param outputSignal the entire output signal with time stamps
     * @param from the time when the current signal starts (non-inclusive)
     * @param to the time when the current signal ends (inclusive). This is the same as the current signal step.
     */
    public ExtendedIOSignalPiece(I inputStep, ValueWithTime<I> outputSignal, double from, double to) {
        super(inputStep, outputSignal.at(to));
        this.previousOutputSignals = outputSignal.range(from, to).getValues();
    }
}
