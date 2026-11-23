package net.maswag.falcaun;

import de.learnlib.sul.SUL;
import net.automatalib.word.Word;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutionException;

/**
 * A {@link SUL} with numerical inputs and outputs.
 * <p>
 * In addition to the step-wise execution defined by {@link SUL}, this interface supports
 * full-word execution through {@link #execute(Word)}.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public interface NumericSUL extends SUL<List<Double>, IOSignalPiece<List<Double>>>, AutoCloseable {
    /**
     * Executes an input word from the initial state and returns its input/output signal.
     * <p>
     * The default implementation calls {@link #pre()}, executes each input using {@link #step(Object)},
     * and calls {@link #post()} in a {@code finally} block. Thus, {@code post()} is called even if
     * a step fails, provided {@code pre()} completed successfully.
     * <p>
     * Implementations may override this method for backend-specific batch execution without individually
     * calling {@code pre()}, {@code step()}, or {@code post()}. Such implementations are responsible for
     * equivalent initialization and cleanup, including when execution fails.
     * <p>
     * Batch execution must not be interleaved with an active step-wise execution session.
     *
     * @param inputSignal the input word
     * @return the corresponding input/output signal, with one output per input symbol
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

    /** {@inheritDoc} */
    default void pre() {
        // do nothing
    }

    /** {@inheritDoc} */
    default void post() {
        // do nothing
    }
}
