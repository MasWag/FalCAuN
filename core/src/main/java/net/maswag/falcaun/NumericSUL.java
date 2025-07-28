package net.maswag.falcaun;

import de.learnlib.sul.SUL;
import net.automatalib.word.Word;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutionException;

/**
 * Systems under learning with numerical I/O.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public interface NumericSUL extends SUL<List<Double>, IOSignalPiece<List<Double>>>, AutoCloseable {
    /**
     * Execute the SUL by feeding the entire input
    */
    default IOSignal<List<Double>> execute(Word<List<Double>> inputSignal) throws InterruptedException, ExecutionException {
        List<List<Double>> outputs = new ArrayList<>();
        this.pre();
        for (List<Double> input : inputSignal) {
            outputs.add(this.step(input).getOutputSignal());
        }
        this.post();
        assert inputSignal.size() == outputs.size();
        return new IODiscreteSignal<>(inputSignal, Word.fromList(outputs));
    }

    /**
     * Returns the number of SUL executions
     */
    int getCounter();

    /**
     * Returns the execution time for the simulations
     */
    double getSimulationTimeSecond();

    /**
     * Clear the counter and the time measure.
     */
    void clear();

    /**
     * Setup SUL.
     */
    default void pre() {
        // do nothing
    }

    /**
     * Shut down SUL.
     */
    default void post() {
        // do nothing
    }
}
