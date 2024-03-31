package net.maswag;

import de.learnlib.api.SUL;
import net.automatalib.words.Word;

import java.util.List;
import java.util.concurrent.ExecutionException;

/**
 * Systems under learning with numerical I/O.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public interface NumericSUL extends SUL<List<Double>, IOSignalPiece>, AutoCloseable {
    /**
     * Execute the SUL by feeding the entire input
    */
    Word<List<Double>> execute(Word<List<Double>> inputSignal) throws InterruptedException, ExecutionException;

    /**
     * Returns the number of SUL executions
     */
    int getCounter();

    /**
     * Returns the execution time for the simulations
     */
    double getSimulationTimeSecond();
}
