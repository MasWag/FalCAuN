package org.group_mmm;

import de.learnlib.api.oracle.PropertyOracle;
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.oracle.equivalence.CExFirstOracle;
import de.learnlib.oracle.property.MealyFinitePropertyOracle;
import lombok.AllArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.automata.transducers.MealyMachine;
import net.automatalib.words.Word;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

@Slf4j
@AllArgsConstructor
class StaticLTLList extends AbstractAdaptiveSTLUpdater {
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
    @Nullable
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
