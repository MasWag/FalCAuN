package net.maswag;


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
     * The previous output signals.
     */
    protected List<I> previousOutputSignals;

    public ExtendedIOSignalPiece(I inputSignal, I outputSignal, List<I> previousOutputSignals) {
        super(inputSignal, outputSignal);
        this.previousOutputSignals = previousOutputSignals;
    }

    /**
     * Constructor for the first signal piece.
     *
     * @param inputStep the current step of the input signal
     * @param outputSignal the entire output signal with time stamps
     * @param from the time when the current signal starts
     * @param to the time when the current signal ends. This is the same as the current signal step.
     */
    public ExtendedIOSignalPiece(I inputStep, ValueWithTime<I> outputSignal, Double from, Double to) {
        super(inputStep, outputSignal.at(to));
        this.previousOutputSignals = outputSignal.range(from, to);
    }
}
