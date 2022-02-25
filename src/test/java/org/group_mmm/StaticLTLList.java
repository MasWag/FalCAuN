package org.group_mmm;

import de.learnlib.api.oracle.PropertyOracle;
import de.learnlib.oracle.property.MealyFinitePropertyOracle;
import lombok.AllArgsConstructor;
import lombok.extern.slf4j.Slf4j;

import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
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
    public List<STLCost> getSTLProperties() {
        return null;
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

    @Override
    protected void notifyFalsifiedProperty(List<Integer> falsifiedIndices) {
        super.notifyFalsifiedProperty(falsifiedIndices);
        disprovedIndices.addAll(falsifiedIndices);
    }

    @Override
    public boolean allDisproved() {
        return ltlProperties.size() == disprovedIndices.size();
    }
}
