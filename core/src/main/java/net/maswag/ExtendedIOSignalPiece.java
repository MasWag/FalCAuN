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
}
