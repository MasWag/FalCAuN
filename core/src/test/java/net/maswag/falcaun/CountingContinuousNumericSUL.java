package net.maswag.falcaun;

import de.learnlib.sul.SUL;
import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * A deterministic continuous-time {@link ContinuousNumericSUL} for tests.
 * <p>
 * The output at time {@code i * signalStep} is the running sum of the first input component up to the {@code i}-th
 * input. Between two sampling points, at time {@code (i - 0.5) * signalStep}, the continuous output has an
 * intermediate sample {@code sum_{i-1} + SPIKE * u_i}. This intermediate sample is visible only through the
 * continuous output signal, e.g., to a derived signal using {@link ExtendedIOSignalPiece#getPreviousOutputSignals()}.
 * Like the Simulink and Python backends, {@link #execute} is a batch execution not using {@link #step}.
 */
class CountingContinuousNumericSUL implements ContinuousNumericSUL {
    static final double SPIKE = 10.0;
    private final double signalStep;
    private int counter = 0;
    private final List<Double> timestamps = new ArrayList<>();
    private final List<List<Double>> values = new ArrayList<>();
    private double sum = 0.0;

    CountingContinuousNumericSUL(double signalStep) {
        this.signalStep = signalStep;
    }

    /**
     * Appends the continuous output for one more input to {@code timestamps} and {@code values}.
     */
    private void append(List<Double> input) {
        int index = timestamps.isEmpty() ? 0 : (int) Math.round(timestamps.get(timestamps.size() - 1) / signalStep) + 1;
        if (index > 0) {
            timestamps.add((index - 0.5) * signalStep);
            values.add(Collections.singletonList(sum + SPIKE * input.get(0)));
        }
        sum += input.get(0);
        timestamps.add(index * signalStep);
        values.add(Collections.singletonList(sum));
    }

    @Override
    public void pre() {
        counter++;
        timestamps.clear();
        values.clear();
        sum = 0.0;
    }

    @Override
    public ExtendedIOSignalPiece<List<Double>> step(List<Double> input) {
        append(input);
        double endTime = timestamps.get(timestamps.size() - 1);
        return new ExtendedIOSignalPiece<>(input, new ValueWithTime<>(new ArrayList<>(timestamps), new ArrayList<>(values)),
                endTime - signalStep, endTime);
    }

    @Override
    public IOContinuousSignal<List<Double>> execute(Word<List<Double>> inputSignal) {
        pre();
        for (List<Double> input : inputSignal) {
            append(input);
        }
        ValueWithTime<List<Double>> continuous = new ValueWithTime<>(new ArrayList<>(timestamps), new ArrayList<>(values));
        WordBuilder<List<Double>> builder = new WordBuilder<>();
        for (int i = 0; i < inputSignal.size(); i++) {
            builder.add(continuous.at(i * signalStep));
        }
        return new IOContinuousSignal<>(inputSignal, builder.toWord(), continuous, signalStep);
    }

    @Override
    public int getCounter() {
        return counter;
    }

    @Override
    public double getSimulationTimeSecond() {
        return 0.0;
    }

    @Override
    public void clear() {
        counter = 0;
    }

    @Override
    public boolean canFork() {
        return false;
    }

    @Override
    public SUL<List<Double>, IOSignalPiece<List<Double>>> fork() {
        throw new UnsupportedOperationException();
    }

    @Override
    public void close() {
    }
}
