package net.maswag.falcaun;

import de.learnlib.exception.SULException;
import de.learnlib.sul.SUL;
import lombok.Getter;
import lombok.Setter;
import net.maswag.falcaun.signal.IOSignalPiece;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

/**
 * A deterministic discrete-time {@link NumericSUL} for tests.
 * <p>
 * The single output is the running sum of the first input component. The SUL records the lifecycle events and
 * counts the sessions (calls of {@link #pre()}) so that tests can check how many times the SUL is actually executed.
 * It does not override {@link NumericSUL#execute}, so the default lifecycle of {@link NumericSUL} is tested.
 */
public class CountingNumericSUL implements NumericSUL {
    /**
     * The lifecycle events in the order of the calls, e.g., {@code pre}, {@code step}, {@code post}.
     */
    @Getter
    private final List<String> events = new ArrayList<>();
    /**
     * The concrete input words of the sessions. The words are recorded at the end of each session.
     */
    @Getter
    private final List<List<List<Double>>> executedInputs = new ArrayList<>();
    private final List<List<Double>> currentInputs = new ArrayList<>();
    private double sum = 0.0;
    private int counter = 0;
    /**
     * If non-negative, {@link #step} fails at this index (0-origin) in each session.
     */
    @Setter
    private int failAtStep = -1;
    /**
     * If true, {@link #pre()} fails.
     */
    @Setter
    private boolean failAtPre = false;

    @Override
    public void pre() {
        events.add("pre");
        if (failAtPre) {
            throw new SULException(new IllegalStateException("pre failed"));
        }
        counter++;
        sum = 0.0;
        currentInputs.clear();
    }

    @Override
    public IOSignalPiece<List<Double>> step(List<Double> input) {
        events.add("step");
        if (currentInputs.size() == failAtStep) {
            throw new SULException(new IllegalStateException("step failed"));
        }
        currentInputs.add(input);
        sum += input.get(0);
        return new IOSignalPiece<>(input, Collections.singletonList(sum));
    }

    @Override
    public void post() {
        events.add("post");
        executedInputs.add(new ArrayList<>(currentInputs));
    }

    @Override
    public int getExecutionCount() {
        return counter;
    }

    @Override
    public double getSimulationTimeSecond() {
        return 0.0;
    }

    @Override
    public void clear() {
        counter = 0;
        events.clear();
        executedInputs.clear();
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
        events.add("close");
    }
}
