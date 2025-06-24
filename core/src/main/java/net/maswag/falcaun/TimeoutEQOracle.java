package net.maswag.falcaun;

import de.learnlib.oracle.EquivalenceOracle;
import de.learnlib.query.DefaultQuery;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.word.Word;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import org.jetbrains.annotations.Nullable;
import java.util.Collection;

/**
 * Am equivalence oracle to add timeout in addition to the original oracle.
 *
 * @param <I> Input symbol
 * @param <O> Output symbol
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class TimeoutEQOracle<I, O> implements EquivalenceOracle.MealyEquivalenceOracle<I, O> {
    private static final Logger LOGGER = LoggerFactory.getLogger(TimeoutEQOracle.class);

    private long timeout;
    private long startTime;
    private MealyEquivalenceOracle<I, O> eqOracle;

    /**
     * @param eqOracle the wrapped equivalence oracle
     * @param timeout  timeout in seconds.
     */
    TimeoutEQOracle(MealyEquivalenceOracle<I, O> eqOracle, long timeout) {
        this.eqOracle = eqOracle;
        this.timeout = timeout * 1000000000;
    }

    /**
     * Start ticking the clock
     */
    void start() {
        startTime = System.nanoTime();
    }

    /** {@inheritDoc} */
    @Nullable
    @Override
    public DefaultQuery<I, Word<O>> findCounterExample(MealyMachine<?, I, ?, O> objects, Collection<? extends I> collection) {
        if ((System.nanoTime() - startTime) > timeout) {
            LOGGER.info("EQQuery finished because of timeout!!");
            return null;
        } else {
            return eqOracle.findCounterExample(objects, collection);
        }
    }
}
