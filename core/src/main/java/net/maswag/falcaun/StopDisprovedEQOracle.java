package net.maswag.falcaun;

import de.learnlib.oracle.EquivalenceOracle;
import de.learnlib.oracle.PropertyOracle;
import de.learnlib.query.DefaultQuery;
import de.learnlib.oracle.equivalence.CExFirstOracle;
import de.learnlib.oracle.property.MealyFinitePropertyOracle;
import lombok.AllArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.word.Word;
import org.jetbrains.annotations.NotNull;

import org.jetbrains.annotations.Nullable;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;


/**
 * Wraps an equivalence oracle so that the equivalence oracle is skipped if all the LTL oracles are disproved.
 *
 * @param <I> Input symbol
 * @param <O> Output symbol
 * @param <C> Type parameter for the AdaptiveSTLUpdater
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class StopDisprovedEQOracle<I, O, C> implements EquivalenceOracle.MealyEquivalenceOracle<I, O> {

    private final AdaptiveSTLUpdater<C> ltlOracles;
    private final MealyEquivalenceOracle<I, O> eqOracle;

    /**
     * @param eqOracle   the wrapped equivalence oracle
     * @param ltlOracles ltlOracles
     */
    StopDisprovedEQOracle(MealyEquivalenceOracle<I, O> eqOracle, AdaptiveSTLUpdater<C> ltlOracles) {
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
    public DefaultQuery<I, Word<O>> findCounterExample(MealyMachine<?, I, ?, O> hypothesis, Collection<? extends I> inputs) {
        if (ltlOracles.allDisproved()) {
            log.debug("A counterexample is already found!!");
            return null;
        } else {
            return eqOracle.findCounterExample(hypothesis, inputs);
        }
    }

    @Slf4j
    @AllArgsConstructor
    static
    class StaticLTLList<I> extends AbstractAdaptiveSTLUpdater<I> {
        List<String> ltlProperties;
        Set<Integer> disprovedIndices = new HashSet<>();

        StaticLTLList(List<String> ltlProperties) {
            this.ltlProperties = ltlProperties;
        }

        @Override
        public List<String> getLTLProperties() {
            return ltlProperties;
        }

        @Override
        public int size() {
            return ltlProperties.size();
        }

        @Override
        public Stream<PropertyOracle.MealyPropertyOracle<String, String, String>> stream() {
            if (Objects.isNull(inclusionOracle) || Objects.isNull(emptinessOracle)) {
                log.error("AbstractAdaptiveSTLUpdater::stream is called before setting inclusionOracle or emptinessOracle");
                throw new NullPointerException();
            }
            return this.getLTLProperties().stream().map(ltl ->
                    new MealyFinitePropertyOracle<>(ltl, inclusionOracle, emptinessOracle, modelChecker));
        }

        /**
         * Find a counter example using the current list of STL formulas
         *
         * @see CExFirstOracle ::findCounterExample
         */
        @org.jetbrains.annotations.Nullable
        @Override
        public DefaultQuery<String, Word<String>> findCounterExample(@NotNull MealyMachine<?, String, ?, String> hypothesis, @NotNull Collection<? extends String> inputs) {
            List<Integer> falsifiedIndices = new ArrayList<>();
            DefaultQuery<String, Word<String>> result = null;
            for (int i = 0; i < this.size(); i++) {
                result = this.stream().collect(Collectors.toList()).get(i).findCounterExample(hypothesis, inputs);
                if (Objects.nonNull(result)) {
                    falsifiedIndices.add(i);
                }
            }
            this.notifyFalsifiedProperty(falsifiedIndices);

            return result;
        }

        @Override
        protected void notifyFalsifiedProperty(List<Integer> falsifiedIndices) {
            super.notifyFalsifiedProperty(falsifiedIndices);
            disprovedIndices.addAll(falsifiedIndices);
        }

        @Override
        public boolean allDisproved() {
            return ltlProperties.size() == disprovedIndices.size();
        }

        @Override
        public void reset() {
            // Since we do not add any STL formula, we do not need to reset.
        }
    }
}
