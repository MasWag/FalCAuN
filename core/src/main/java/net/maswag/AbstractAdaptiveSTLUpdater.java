package net.maswag;

import de.learnlib.oracle.EmptinessOracle;
import de.learnlib.oracle.InclusionOracle;
import de.learnlib.oracle.MembershipOracle;
import de.learnlib.oracle.PropertyOracle;
import de.learnlib.oracle.emptiness.MealyBFEmptinessOracle;
import de.learnlib.oracle.equivalence.MealyBFInclusionOracle;
import de.learnlib.oracle.property.LoggingPropertyOracle;
import de.learnlib.oracle.property.MealyFinitePropertyOracle;
import de.learnlib.query.DefaultQuery;
import lombok.Getter;
import lombok.Setter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.modelchecker.ltsmin.monitor.LTSminMonitorIOBuilder;
import net.automatalib.modelchecking.ModelChecker;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.word.Word;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Abstract class for potentially adaptive set of STL formulas
 *
 * @author Masaki Waga
 * @param <I> Type of the input at each step
 * @see BlackBoxVerifier
 * @see NumericSULVerifier
 */
@Slf4j
public abstract class AbstractAdaptiveSTLUpdater<I> implements AdaptiveSTLUpdater<I> {
    protected static final Function<String, String> EDGE_PARSER = s -> s;
    protected EmptinessOracle.MealyEmptinessOracle<String, String> emptinessOracle;
    @NotNull
    protected ModelChecker.MealyModelChecker<String, String, String, MealyMachine<?, String, ?, String>> modelChecker;
    protected InclusionOracle.MealyInclusionOracle<String, String> inclusionOracle;
    protected MembershipOracle.MealyMembershipOracle<String, String> memOracle;
    @Setter
    protected Alphabet<String> inputAlphabet;
    @Getter
    private final List<TemporalLogic<I>> STLProperties = new ArrayList<>();
    private final List<PropertyOracle.MealyPropertyOracle<String, String, String>> propertyOracles = new ArrayList<>();
    boolean initialized = false;
    // The list of the STL formulas that are already falsified.
    private final List<TemporalLogic<I>> reportedFormulas = new ArrayList<>();

    public AbstractAdaptiveSTLUpdater() {
        // Create model checker
        modelChecker = new LTSminMonitorIOBuilder<String, String>().withString2Input(EDGE_PARSER).withString2Output(EDGE_PARSER).create();
    }

    //@ requires inclusionOracle != null && emptinessOracle != null
    @Override
    public Stream<PropertyOracle.MealyPropertyOracle<String, String, String>> stream() {
        confirmInitialization();
        assert STLProperties.size() == propertyOracles.size();
        return propertyOracles.stream();
    }

    @Override
    public List<PropertyOracle<String, ? super MealyMachine<?, String, ?, String>, ?, Word<String>>> getPropertyOracles() {
        return new ArrayList<>(propertyOracles);
    }

    public void setMemOracle(@NotNull MembershipOracle.MealyMembershipOracle<String, String> memOracle) {
        this.memOracle = memOracle;
        // create an emptiness oracle, that is used to disprove properties
        double multiplier = 1.0;
        emptinessOracle = new MealyBFEmptinessOracle<>(this.memOracle, multiplier);

        // create an inclusion oracle, that is used to find counterexamples to hypotheses
        inclusionOracle = new MealyBFInclusionOracle<>(this.memOracle, multiplier);
    }

    protected void addSTLProperty(TemporalLogic<I> stl) {
        if (STLProperties.contains(stl)) {
            return;
        }
        this.STLProperties.add(stl);
        if (initialized && Objects.nonNull(inclusionOracle) && Objects.nonNull(emptinessOracle)) {
            propertyOracles.add(
                    new LoggingPropertyOracle.MealyLoggingPropertyOracle<>(
                            new MealyFinitePropertyOracle<>(stl.toLTLString(), inclusionOracle, emptinessOracle, modelChecker)));
        }
    }

    protected void addSTLProperties(Collection<? extends TemporalLogic<I>> stlCollection) {
        stlCollection.forEach(this::addSTLProperty);
    }

    protected void removeSTLProperty(int index) {
        this.getSTLProperties().remove(index);
        if (!initialized) {
            log.warn("STL property list is not initialized yet. This should happen only in testing.");
            return;
        }
        this.propertyOracles.remove(index);
    }

    protected void removeSTLProperties(Collection<Integer> indices) {
        indices.stream().sorted(Comparator.reverseOrder()).forEach(this::removeSTLProperty);
    }

    /**
     * Initialize property oracles if they are not initialized yet.
     * <p>
     * We do not initialize it in the constructor to delay the construction of the membership oracle.
     */
    private void confirmInitialization() {
        if (Objects.isNull(inclusionOracle) || Objects.isNull(emptinessOracle)) {
            log.error("AbstractAdaptiveSTLUpdater::confirmInitialization is called before setting inclusionOracle or emptinessOracle");
            throw new NullPointerException();
        }
        if (!initialized) {
            STLProperties.forEach(stl ->
                    propertyOracles.add(
                            new LoggingPropertyOracle.MealyLoggingPropertyOracle<>(
                                    new MealyFinitePropertyOracle<>(stl.toLTLString(),
                                            inclusionOracle, emptinessOracle, modelChecker))));
            initialized = true;
        }
    }

    public final boolean newlyFalsifiedFormula(TemporalLogic<I> stlFormula) {
        return !reportedFormulas.contains(stlFormula);
    }

    /**
     * Try to disprove the current list of STL formulas against the given Mealy machine.
     * <p>
     * It returns
     * <ul>
     *     <li>a counterexample for the newly falsified STL formula, if exists</li>
     *     <li>a counterexample for the first falsified STL formula, if exists</li>
     *     <li>null, if no counterexample is found.</li>
     * </ul>
     * We call notifyFalsifiedProperty with the indices of the truly falsified formulas.
     *
     * @param hypothesis The Mealy machine to be verified.
     * @param inputs     The alphabet of the Mealy machine.
     * @return A query of counterexample if a counterexample is found. Otherwise, it returns null.
     * @see de.learnlib.oracle.equivalence.CExFirstOracle
     */
    @Nullable
    @Override
    public DefaultQuery<String, Word<String>> findCounterExample(@NotNull MealyMachine<?, String, ?, String> hypothesis, @NotNull Collection<? extends String> inputs) {
        confirmInitialization();
        log.debug("Current list of STL formulas: {}", STLProperties);
        List<Integer> falsifiedIndices = new ArrayList<>();
        DefaultQuery<String, Word<String>> newFalsifiedResult = null;
        DefaultQuery<String, Word<String>> falsifiedResult = null;
        for (int i = 0; i < this.size(); i++) {
            DefaultQuery<String, Word<String>> result = this.propertyOracles.get(i).findCounterExample(hypothesis, inputs);
            if (Objects.nonNull(result)) {
                boolean isTrueCounterExample = this.propertyOracles.get(i).isDisproved();
                if (Objects.isNull(falsifiedResult)) {
                    falsifiedResult = result;
                }
                if (isTrueCounterExample) {
                    log.debug("STL formula {} was disproved.", STLProperties.get(i));
                    falsifiedIndices.add(i);
                } else {
                    log.debug("Found a spurious counterexample for STL formula {}.", STLProperties.get(i));
                }
                if (newlyFalsifiedFormula(getSTLProperties().get(i))) {
                    // We report a new falsified formula if exists
                    newFalsifiedResult = result;
                    if (isTrueCounterExample) {
                        reportedFormulas.add(getSTLProperties().get(i));
                    }
                    break;
                }
            } else if (this.propertyOracles.get(i).isDisproved()) {
              log.debug("STL formula {} was disproved.", STLProperties.get(i));
                reportedFormulas.add(getSTLProperties().get(i));
                falsifiedIndices.add(i);
            } else {
                log.debug("STL formula {} was NOT disproved.", STLProperties.get(i));
            }
        }
        if (!falsifiedIndices.isEmpty()) {
            this.notifyFalsifiedProperty(falsifiedIndices);
        }
        if (Objects.nonNull(newFalsifiedResult)) {
            return newFalsifiedResult;
        } else {
            return falsifiedResult;
        }
    }

    /**
     * Notify that this.getLTLProperties.get(i) is falsified by the currently learned model.
     * <p>
     * Typically, we can generate a new adaptive formula.
     * Note: we should not remove the original formula by this.
     *
     * @param falsifiedIndices The set of indices of the falsified LTL formulas
     */
    protected void notifyFalsifiedProperty(List<Integer> falsifiedIndices) {
    }

    @Override
    public String toString() {
        // Map the list of STL properties to a list of strings and join them with a comma.
        return "[" + this.getSTLProperties().stream().map(TemporalLogic::toString).collect(Collectors.joining(", ")) + "]";
    }
}
