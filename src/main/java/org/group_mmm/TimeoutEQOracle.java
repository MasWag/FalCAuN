package org.group_mmm;

import de.learnlib.api.oracle.EquivalenceOracle;
import de.learnlib.api.query.DefaultQuery;
import net.automatalib.automata.transducers.MealyMachine;
import net.automatalib.words.Word;

import javax.annotation.Nullable;
import javax.annotation.ParametersAreNullableByDefault;
import java.util.Collection;

/**
 * Am equivalence oracle to add timeout in addition to the original oracle.
 *
 * @param <I> Input symbol
 * @param <O> Output symbol
 */
public class TimeoutEQOracle<I, O> implements EquivalenceOracle.MealyEquivalenceOracle<I, O> {
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

    @Nullable
    @Override
    @ParametersAreNullableByDefault
    public DefaultQuery<I, Word<O>> findCounterExample(MealyMachine<?, I, ?, O> objects, Collection<? extends I> collection) {
        if ((System.nanoTime() - startTime) > timeout) {
            return null;
        } else {
            return eqOracle.findCounterExample(objects, collection);
        }
    }
}
