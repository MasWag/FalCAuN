package org.group_mmm;

import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.oracle.PropertyOracle;
import de.learnlib.api.query.DefaultQuery;
import lombok.AllArgsConstructor;
import net.automatalib.automata.transducers.MealyMachine;
import net.automatalib.words.Word;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Collection;
import java.util.List;
import java.util.stream.Stream;

@AllArgsConstructor
class StaticLTLList implements AdaptiveSTLUpdater {
    List<String> ltlProperties;

    @Override
    public List<STLCost> getSTLProperties() {
        return null;
    }

    @Override
    public List<String> getLTLProperties() {
        return ltlProperties;
    }

    @Override
    public List<PropertyOracle.MealyPropertyOracle<String, String, String>> list() {
        return null;
    }

    @Override
    public Stream<PropertyOracle.MealyPropertyOracle<String, String, String>> stream() {
        return null;
    }

    @Override
    public int size() {
        return 0;
    }

    @Override
    public void setMemOracle(MembershipOracle.@NotNull MealyMembershipOracle<String, String> memOracle) {

    }

    @Override
    public List<PropertyOracle<String, ? super MealyMachine<?, String, ?, String>, ?, Word<String>>> getPropertyOracles() {
        return null;
    }

    @Nullable
    @Override
    public DefaultQuery<String, Word<String>> findCounterExample(@NotNull MealyMachine<?, String, ?, String> objects, @NotNull Collection<? extends String> collection) {
        return null;
    }
}
