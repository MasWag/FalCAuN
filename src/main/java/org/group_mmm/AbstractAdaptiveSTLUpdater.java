package org.group_mmm;

import de.learnlib.api.oracle.EmptinessOracle;
import de.learnlib.api.oracle.InclusionOracle;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.oracle.PropertyOracle;
import de.learnlib.api.query.DefaultQuery;
import de.learnlib.oracle.emptiness.MealyBFEmptinessOracle;
import de.learnlib.oracle.equivalence.MealyBFInclusionOracle;
import de.learnlib.oracle.property.MealyFinitePropertyOracle;
import lombok.Setter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.automata.transducers.MealyMachine;
import net.automatalib.modelcheckers.ltsmin.monitor.LTSminMonitorIOBuilder;
import net.automatalib.modelchecking.ModelChecker;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
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
    @Setter
    protected Alphabet<String> inputAlphabet;

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
        return this.stream().collect(Collectors.toList());
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
                new MealyFinitePropertyOracle<>(stl.toLTLString(), inclusionOracle, emptinessOracle, modelChecker));
    }

    @Override
    public List<PropertyOracle.MealyPropertyOracle<String, String, String>> list() {
        return this.stream().collect(Collectors.toList());
    }

    @Override
    public int size() {
        return this.getSTLProperties().size();
    }

    /**
     * Find a counter example using the current list of STL formulas
     */
    @Nullable
    @Override
    public DefaultQuery<String, Word<String>> findCounterExample(@NotNull MealyMachine<?, String, ?, String> hypothesis, @NotNull Collection<? extends String> inputs) {
        DefaultQuery<String, Word<String>> result = null;
        for (int i = 0; i < this.size(); i++) {
            result = this.getPropertyOracles().get(i).findCounterExample(hypothesis, inputs);
            if (Objects.nonNull(result)) {
                break;
            }
        }
        assert Objects.isNull(result) || this.isCounterExample(hypothesis, result.getInput(), result.getOutput());
        if (Objects.isNull(result)) {
            List<Integer> falsifiedIndices = new ArrayList<>();
            for (int i = 0; i < this.size(); i++) {
                final MealyMachine<?, String, ?, String> cexMealyCandidate =
                        modelChecker.findCounterExample(hypothesis, this.inputAlphabet, this.getLTLProperties().get(i));
                if (Objects.nonNull(cexMealyCandidate)) {
                    falsifiedIndices.add(i);
                }
            }
            this.notifyFalsifiedProperty(falsifiedIndices);
        }
        return result;
    }

    /**
     * Notify that this.getLTLProperties.get(i) is falsified by the currently learned model.
     *
     * @param falsifiedIndices The set of indices of the falsified LTL formulas
     */
    protected void notifyFalsifiedProperty(List<Integer> falsifiedIndices) {
    }
}
