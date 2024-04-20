package net.maswag;

import de.learnlib.sul.SUL;
import net.automatalib.word.Word;

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
    IOSignal<List<Double>> execute(Word<List<Double>> inputSignal) throws InterruptedException, ExecutionException;

    /**
     * Returns the number of SUL executions
     */
    int getCounter();

    /**
     * Returns the execution time for the simulations
     */
    double getSimulationTimeSecond();
}
