package net.maswag.falcaun;

import de.learnlib.sul.SUL;
import net.automatalib.word.Word;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutionException;

/**
 * Systems under learning with numerical I/O.
 *
 * <h2>Execution lifecycle</h2>
 * <ul>
 *     <li>{@link #pre()} starts an execution session from the initial state of the system.</li>
 *     <li>{@link #step(Object)} executes one step within the current session.</li>
 *     <li>{@link #post()} finalizes the current session. It must be called once for each successful call of
 *     {@link #pre()}, even if a step fails.</li>
 *     <li>{@link #execute(Word)} runs a complete session for the given input word, including the finalization.
 *     Implementations may override it to use a backend-specific batch execution, but it must not leave an
 *     unfinalized session behind, even if the execution fails.</li>
 * </ul>
 * A session started by {@link #pre()} and a session of {@link #execute(Word)} must not be interleaved.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public interface NumericSUL extends SUL<List<Double>, IOSignalPiece<List<Double>>>, AutoCloseable {
    /**
     * Execute the SUL by feeding the entire input.
     * <p>
     * The default implementation calls {@link #pre()}, {@link #step(Object)} for each input, and {@link #post()}.
     * If {@link #pre()} succeeds, {@link #post()} is called even if a step fails.
     *
     * @param inputSignal the input signal
     * @return the input and output signals. The size of the output signal is the same as that of the input signal.
     */
    default IOSignal<List<Double>> execute(Word<List<Double>> inputSignal) throws InterruptedException, ExecutionException {
        List<List<Double>> outputs = new ArrayList<>();
        this.pre();
        try {
            for (List<Double> input : inputSignal) {
                outputs.add(this.step(input).getOutputSignal());
            }
        } finally {
            this.post();
        }
        assert inputSignal.size() == outputs.size();
        return new IODiscreteSignal<>(inputSignal, Word.fromList(outputs));
    }

    /**
     * Returns the number of the executions of the SUL.
     * <p>
     * What is counted as an execution is backend specific. Typically, it is the number of the sessions, i.e.,
     * the calls of {@link #pre()} or {@link #execute(Word)}.
     */
    int getExecutionCount();

    /**
     * Returns the execution time for the simulations
     */
    double getSimulationTimeSecond();

    /**
     * Clear the counter and the time measure.
     */
    void clear();

    /**
     * Starts an execution session.
     */
    default void pre() {
        // do nothing
    }

    /**
     * Finalizes the current execution session.
     */
    default void post() {
        // do nothing
    }
}
