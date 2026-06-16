package net.maswag.falcaun;

import de.learnlib.oracle.EquivalenceOracle;
import de.learnlib.query.DefaultQuery;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.word.Word;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import org.jetbrains.annotations.Nullable;
import java.util.Collection;
import java.util.concurrent.TimeUnit;
import java.util.function.LongSupplier;

/**
 * Am equivalence oracle to add timeout in addition to the original oracle.
 *
 * @param <I> Input symbol
 * @param <O> Output symbol
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class TimeoutEQOracle<I, O> implements EquivalenceOracle.MealyEquivalenceOracle<I, O> {
    private static final Logger LOGGER = LoggerFactory.getLogger(TimeoutEQOracle.class);

    private final long timeout;
    private long startTime;
    private final MealyEquivalenceOracle<I, O> eqOracle;
    /**
     * Clock supplier for reading the current time.
     * In production this is {@link System#nanoTime()}; for testing it may be a fake
     * clock (e.g. returning synthetic nanosecond values) so that timeout behaviour
     * can be verified without sleeping or wall-clock timing.
     */
    private final LongSupplier nanoTime;

    /**
     * @param eqOracle the wrapped equivalence oracle
     * @param timeout  timeout in seconds.
     */
    TimeoutEQOracle(MealyEquivalenceOracle<I, O> eqOracle, long timeout) {
        this(eqOracle, timeout, System::nanoTime);
    }

    /**
     * @param eqOracle the wrapped equivalence oracle
     * @param timeout  timeout in seconds.
     * @param nanoTime a {@link LongSupplier} that returns current time in nanoseconds.
     *                 In production this is typically {@code System::nanoTime};
     *                 for testing provide a fake clock that returns controllable values
     *                 (e.g. {@code () -> fakeClockValue}) so timeout behaviour can be
     *                 verified without sleeping or wall-clock timing.
     */
    TimeoutEQOracle(MealyEquivalenceOracle<I, O> eqOracle, long timeout, LongSupplier nanoTime) {
        this.eqOracle = eqOracle;
        this.timeout = TimeUnit.SECONDS.toNanos(timeout);
        this.nanoTime = nanoTime;
    }

    /**
     * Start ticking the clock
     */
    void start() {
        startTime = nanoTime.getAsLong();
    }

    /** {@inheritDoc} */
    @Nullable
    @Override
    public DefaultQuery<I, Word<O>> findCounterExample(MealyMachine<?, I, ?, O> objects, Collection<? extends I> collection) {
        if ((nanoTime.getAsLong() - startTime) > timeout) {
            LOGGER.info("EQQuery finished because of timeout!!");
            return null;
        } else {
            return eqOracle.findCounterExample(objects, collection);
        }
    }
}
