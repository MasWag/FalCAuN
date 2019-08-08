package org.group_mmm;

import de.learnlib.api.oracle.EquivalenceOracle;
import de.learnlib.api.oracle.PropertyOracle;
import de.learnlib.api.query.DefaultQuery;
import net.automatalib.automata.transducers.MealyMachine;
import net.automatalib.words.Word;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.annotation.Nullable;
import javax.annotation.ParametersAreNullableByDefault;
import java.util.Collection;
import java.util.List;


/**
 * Am equivalence oracle to add isDisproved in addition to the original oracle.
 *
 * @param <I> Input symbol
 * @param <O> Output symbol
 */
public class StopDisprovedEQOracle<I, O> implements EquivalenceOracle.MealyEquivalenceOracle<I, O> {
    private static final Logger LOGGER = LoggerFactory.getLogger(org.group_mmm.StopDisprovedEQOracle.class);

    private List<PropertyOracle.MealyPropertyOracle<String, String, String>> ltlOracles;
    private MealyEquivalenceOracle<I, O> eqOracle;

    /**
     * @param eqOracle   the wrapped equivalence oracle
     * @param ltlOracles ltlOracles
     */
    StopDisprovedEQOracle(MealyEquivalenceOracle<I, O> eqOracle, List<PropertyOracle.MealyPropertyOracle<String, String, String>> ltlOracles) {
        this.eqOracle = eqOracle;
        this.ltlOracles = ltlOracles;
    }

    @Nullable
    @Override
    @ParametersAreNullableByDefault
    public DefaultQuery<I, Word<O>> findCounterExample(MealyMachine<?, I, ?, O> objects, Collection<? extends I> collection) {
        if (ltlOracles.stream().allMatch(PropertyOracle.MealyPropertyOracle::isDisproved)) {
            LOGGER.debug("A counterexample is already found!!");
            return null;
        } else {
            return eqOracle.findCounterExample(objects, collection);
        }
    }
}
