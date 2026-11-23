package net.maswag.falcaun.oracle;

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
 * An equivalence oracle to add timeout in addition to the original oracle.
 * <p>
 * The timeout is checked only when {@link #findCounterExample} is called: if the elapsed time since {@link #start()}
 * exceeds the timeout, the wrapped oracle is skipped. An ongoing invocation of the wrapped oracle is not interrupted,
 * so this is not a strict timeout of the entire black-box checking.
 *
 * @param <I> Input symbol
 * @param <O> Output symbol
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class TimeoutEQOracle<I, O> implements EquivalenceOracle.MealyEquivalenceOracle<I, O> {
    private static final Logger LOGGER = LoggerFactory.getLogger(TimeoutEQOracle.class);

    private final long timeout;
    private long startTime;
    /**
     * Whether the wrapped oracle has been skipped because of the timeout since the last {@link #start()}.
     */
    private boolean timedOut = false;
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
    public TimeoutEQOracle(MealyEquivalenceOracle<I, O> eqOracle, long timeout) {
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
    public void start() {
        startTime = nanoTime.getAsLong();
        timedOut = false;
    }

    /**
     * @return {@code true} if and only if the wrapped oracle has been skipped because of the timeout since the last {@link #start()}.
     */
    public boolean hasTimedOut() {
        return timedOut;
    }

    /** {@inheritDoc} */
    @Nullable
    @Override
    public DefaultQuery<I, Word<O>> findCounterExample(MealyMachine<?, I, ?, O> objects, Collection<? extends I> collection) {
        if ((nanoTime.getAsLong() - startTime) > timeout) {
            LOGGER.info("EQQuery finished because of timeout!!");
            timedOut = true;
            return null;
        } else {
            return eqOracle.findCounterExample(objects, collection);
        }
    }
}
