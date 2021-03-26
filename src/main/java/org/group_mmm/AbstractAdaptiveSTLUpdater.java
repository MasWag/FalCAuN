package org.group_mmm;

import de.learnlib.api.oracle.EmptinessOracle;
import de.learnlib.api.oracle.InclusionOracle;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.oracle.PropertyOracle;
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.oracle.emptiness.MealyBFEmptinessOracle;
import de.learnlib.oracle.equivalence.MealyBFInclusionOracle;
import de.learnlib.oracle.property.MealyFinitePropertyOracle;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.automata.transducers.MealyMachine;
import net.automatalib.modelcheckers.ltsmin.monitor.LTSminMonitorIOBuilder;
import net.automatalib.modelchecking.ModelChecker;
import net.automatalib.words.Word;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.Collection;
import java.util.List;
import java.util.Objects;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Abstract class for potentially adaptive set of STL formulas
 *
 * @author Masaki Waga
 * @see BlackBoxVerifier
 * @see SimulinkVerifier
 */
@Slf4j
public abstract class AbstractAdaptiveSTLUpdater implements AdaptiveSTLUpdater {
    protected static final Function<String, String> EDGE_PARSER = s -> s;
    protected EmptinessOracle.MealyEmptinessOracle<String, String> emptinessOracle;
    @NotNull
    protected ModelChecker.MealyModelChecker<String, String, String, MealyMachine<?, String, ?, String>> modelChecker;
    protected InclusionOracle.MealyInclusionOracle<String, String> inclusionOracle;
    protected MembershipOracle.MealyMembershipOracle<String, String> memOracle;

    public AbstractAdaptiveSTLUpdater() {
        // Create model checker
        modelChecker = new LTSminMonitorIOBuilder<String, String>()
                .withString2Input(EDGE_PARSER).withString2Output(EDGE_PARSER).create();
    }

    public void setMemOracle(@NotNull MembershipOracle.MealyMembershipOracle<String, String> memOracle) {
        this.memOracle = memOracle;
        // create an emptiness oracle, that is used to disprove properties
        double multiplier = 1.0;
        emptinessOracle = new MealyBFEmptinessOracle<>(this.memOracle, multiplier);

        // create an inclusion oracle, that is used to find counterexamples to hypotheses
        inclusionOracle = new MealyBFInclusionOracle<>(this.memOracle, multiplier);
    }

    @Override
    public List<PropertyOracle<String, ? super MealyMachine<?, String, ?, String>, ?, Word<String>>> getPropertyOracles() {
        return this.getSTLProperties().stream().map(stl ->
                new MealyFinitePropertyOracle<>(stl.toAbstractString(), inclusionOracle, emptinessOracle, modelChecker)).collect(Collectors.toList());
    }

    @Override
    public List<String> getLTLProperties() {
        return this.getSTLProperties().stream().map(STLCost::toLTLString).collect(Collectors.toList());
    }

    //@ requires inclusionOracle != null && emptinessOracle != null
    @Override
    public Stream<PropertyOracle.MealyPropertyOracle<String, String, String>> stream() {
        if (Objects.isNull(inclusionOracle) || Objects.isNull(emptinessOracle)) {
            log.error("AbstractAdaptiveSTLUpdater::stream is called before setting inclusionOracle or emptinessOracle");
            throw new NullPointerException();
        }
        return this.getSTLProperties().stream().map(stl ->
                new MealyFinitePropertyOracle<>(stl.toAbstractString(), inclusionOracle, emptinessOracle, modelChecker));
    }

    @Override
    public List<PropertyOracle.MealyPropertyOracle<String, String, String>> list() {
        return this.stream().collect(Collectors.toList());
    }

    @Override
    public int size() {
        return this.getSTLProperties().size();
    }

    @Nullable
    @Override
    public DefaultQuery<String, Word<String>> findCounterExample(@NotNull MealyMachine<?, String, ?, String> hypothesis, @NotNull Collection<? extends String> inputs) {
        DefaultQuery<String, Word<String>> result = this.getPropertyOracles().stream().map(propertyOracle ->
                propertyOracle.findCounterExample(hypothesis, inputs)).findFirst().orElse(null);
        assert !Objects.nonNull(result) || this.isCounterExample(hypothesis, result.getInput(), result.getOutput());
        return result;
    }
}
