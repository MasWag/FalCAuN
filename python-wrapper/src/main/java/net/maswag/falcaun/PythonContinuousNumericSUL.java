package net.maswag.falcaun;

import lombok.Getter;
import net.automatalib.word.Word;

import javax.annotation.Nullable;

import java.util.List;
import java.util.concurrent.ExecutionException;


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
     * {@inheritDoc}
     */
    @Override
    public IOContinuousSignal<List<Double>> execute(Word<List<Double>> inputSignal)
            throws InterruptedException, ExecutionException {
        return execute_aux(inputSignal);
    }

}
