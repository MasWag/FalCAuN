package org.group_mmm;

import de.learnlib.api.oracle.EquivalenceOracle;
import de.learnlib.api.oracle.PropertyOracle;
import de.learnlib.api.query.DefaultQuery;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.automata.transducers.MealyMachine;
import net.automatalib.words.Word;

import javax.annotation.Nullable;
import javax.annotation.ParametersAreNullableByDefault;
import java.util.Collection;


/**
 * Am equivalence oracle to add isDisproved in addition to the original oracle.
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

    /** {@inheritDoc} */
    @Nullable
    @Override
    @ParametersAreNullableByDefault
    public DefaultQuery<I, Word<O>> findCounterExample(MealyMachine<?, I, ?, O> objects, Collection<? extends I> collection) {
        if (ltlOracles.stream().allMatch(PropertyOracle.MealyPropertyOracle::isDisproved)) {
            log.debug("A counterexample is already found!!");
            return null;
        } else {
            return eqOracle.findCounterExample(objects, collection);
        }
    }
}
