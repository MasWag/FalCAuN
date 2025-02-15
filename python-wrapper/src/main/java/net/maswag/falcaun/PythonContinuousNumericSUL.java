package net.maswag.falcaun;

import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.word.Word;

import javax.annotation.Nullable;

import java.util.List;
import java.util.concurrent.ExecutionException;

/**
 * The System Under Learning implemented by a Simulink. We use the fixed step
 * execution of Simulink to make sampling easier.
 */
@Slf4j
public class PythonContinuousNumericSUL extends PythonNumericSUL implements ContinuousNumericSUL {
    @Getter
    private int counter = 0;

    public PythonContinuousNumericSUL(String initScript, Double signalStep)
            throws InterruptedException, ExecutionException {
        super(initScript, signalStep);
    }

    /**
     * {@inheritDoc}
     */
    @Nullable
    @Override
    public ExtendedIOSignalPiece<List<Double>> step(@Nullable List<Double> inputSignal) {
        return super.step_aux(inputSignal);

    }

    /**
     * Execute the Simulink model by feeding inputSignal
     * <p>
     * For inputSignal = a1, a2, ..., an, we construct a timed word w = (a1, 0),
     * (a2, T), (a3, 2 * T), ... (an, (n - 1) * T) and execute the Simulink model by
     * feeding the piecewise-linear interpolation of w.
     *
     * @param inputSignal The input signal
     * @return The output signal. The size is same as the input.
     */
    @Override
    public IOContinuousSignal<List<Double>> execute(Word<List<Double>> inputSignal)
            throws InterruptedException, ExecutionException {
        return execute_aux(inputSignal);
    }

}
