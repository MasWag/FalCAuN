package org.group_mmm;

import de.learnlib.api.oracle.EquivalenceOracle;
import de.learnlib.api.query.DefaultQuery;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.automata.transducers.MealyMachine;
import net.automatalib.words.Word;

import javax.annotation.Nullable;
import javax.annotation.ParametersAreNonnullByDefault;
import java.util.Collection;


/**
 * Wraps an equivalence oracle so that the equivalence oracle is skipped if all the LTL oracles are disproved.
 *
 * @param <I> Input symbol
 * @param <O> Output symbol
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class StopDisprovedEQOracle<I, O> implements EquivalenceOracle.MealyEquivalenceOracle<I, O> {

    private final AdaptiveSTLUpdater ltlOracles;
    private final MealyEquivalenceOracle<I, O> eqOracle;

    /**
     * @param eqOracle   the wrapped equivalence oracle
     * @param ltlOracles ltlOracles
     */
    StopDisprovedEQOracle(MealyEquivalenceOracle<I, O> eqOracle, AdaptiveSTLUpdater ltlOracles) {
        this.eqOracle = eqOracle;
        this.ltlOracles = ltlOracles;
    }

    /**
     * {@inheritDoc}
     * <p>
     * This function skip running an equivalence query if all the LTL oracles are disproved.
     */
    @Nullable
    @Override
    @ParametersAreNonnullByDefault
    public DefaultQuery<I, Word<O>> findCounterExample(MealyMachine<?, I, ?, O> hypothesis, Collection<? extends I> inputs) {
        if (ltlOracles.allDisproved()) {
            log.debug("A counterexample is already found!!");
            return null;
        } else {
            return eqOracle.findCounterExample(hypothesis, inputs);
        }
    }
}
