package net.maswag;

import net.automatalib.word.Word;

import java.util.List;
import java.util.concurrent.ExecutionException;

/**
 * Continuous-time systems under learning with numerical I/O.
 */
public interface ContinuousNumericSUL extends NumericSUL {
    /**
     * Execute the SUL by feeding single step input.
     *
     * @param inputSignal the input signal at one time step
     * @return the output signal at one time step with the previous output signals
     */
    @Override
    ExtendedIOSignalPiece<List<Double>> step(List<Double> inputSignal);

    @Override
    IOContinuousSignal<List<Double>> execute(Word<List<Double>> inputSignal) throws InterruptedException, ExecutionException;
}
