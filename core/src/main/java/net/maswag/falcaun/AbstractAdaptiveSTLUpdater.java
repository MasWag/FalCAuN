package net.maswag.falcaun;

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
import net.maswag.falcaun.parser.TemporalLogic;

import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Abstract class representing a potentially adaptive set of Signal Temporal Logic (STL) formulas.
 * This class provides a framework for updating and verifying STL properties in a system, allowing for dynamic adaptation based on new information or changes in the system's behavior.
 *
 * @author Masaki Waga
 * @param <I> Type of the input at each step
 * @see BlackBoxVerifier
 * @see NumericSULVerifier
 */
@Slf4j
public abstract class AbstractAdaptiveSTLUpdater<I> implements AdaptiveSTLUpdater<I> {
    /**
     * A function that parses edge labels in the model checker.
     * This identity function is used to convert string representations to and from the model checker's internal format.
     */
    protected static final Function<String, String> EDGE_PARSER = s -> s;
    /**
     * The oracle used to check for the emptiness of a language, which is essential for disproving properties.
     */
    protected EmptinessOracle.MealyEmptinessOracle<String, String> emptinessOracle;
    /**
     * The model checker used to verify properties against a Mealy machine, ensuring that the system meets specified Signal Temporal Logic (STL) requirements.
     */
    @NotNull
    protected ModelChecker.MealyModelChecker<String, String, String, MealyMachine<?, String, ?, String>> modelChecker;
    /**
     * The oracle used to check for the inclusion of one language in another, which is essential for finding counterexamples to hypotheses.
     */
    protected InclusionOracle.MealyInclusionOracle<String, String> inclusionOracle;
    /**
     * The oracle used to query membership in the language recognized by a Mealy machine, determining whether specific input sequences produce expected outputs.
     */
    protected MembershipOracle.MealyMembershipOracle<String, String> memOracle;
    /**
     * The alphabet of input symbols used by the Mealy machine, defining the set of valid inputs for the system.
     */
    @Setter
    protected Alphabet<String> inputAlphabet;
    /**
     * A list of Signal Temporal Logic (STL) properties that need to be verified against the system.
     */
    @Getter
    private final List<TemporalLogic<I>> STLProperties = new ArrayList<>();
    /**
     * A list of property oracles used to verify the Signal Temporal Logic (STL) properties against the system.
     */
    private final List<PropertyOracle.MealyPropertyOracle<String, String, String>> propertyOracles = new ArrayList<>();
    /**
     * Flag indicating whether the property oracles have been initialized.
     */
    /**
     * Flag indicating whether the property oracles have been initialized and are ready for use.
     */
    boolean initialized = false;
    /**
     * A list of Signal Temporal Logic (STL) formulas that have been disproved by the verification process.
     */
    private final List<TemporalLogic<I>> reportedFormulas = new ArrayList<>();

    /**
     * Constructs an instance of {@link AbstractAdaptiveSTLUpdater}.
     *
     * Initializes the model checker used to verify properties against a Mealy machine.
     */
    public AbstractAdaptiveSTLUpdater() {
        // Create model checker
        modelChecker = new LTSminMonitorIOBuilder<String, String>()
                .withString2Input(EDGE_PARSER)
                .withString2Output(EDGE_PARSER)
                .create();
    }

    //@ requires inclusionOracle != null && emptinessOracle != null
    /**
     * Returns a stream of property oracles used to verify the Signal Temporal Logic (STL) properties.
     *
     * @return A stream of {@link PropertyOracle.MealyPropertyOracle} instances.
     */
    @Override
    public Stream<PropertyOracle.MealyPropertyOracle<String, String, String>> stream() {
        confirmInitialization();
        assert STLProperties.size() == propertyOracles.size();
        return propertyOracles.stream();
    }

    /**
     * Returns a list of property oracles used to verify the Signal Temporal Logic (STL) properties.
     *
     * @return A list of {@link PropertyOracle.MealyPropertyOracle} instances.
     */
    @Override
    public List<PropertyOracle<String, ? super MealyMachine<?, String, ?, String>, ?, Word<String>>> getPropertyOracles() {
        return new ArrayList<>(propertyOracles);
    }

    /**
     * Sets the membership oracle and initializes the emptiness and inclusion oracles.
     *
     * @param memOracle The membership oracle to set.
     */
    public void setMemOracle(@NotNull MembershipOracle.MealyMembershipOracle<String, String> memOracle) {
        this.memOracle = memOracle;
        // Create an emptiness oracle used to disprove properties
        double multiplier = 1.0;
        emptinessOracle = new MealyBFEmptinessOracle<>(this.memOracle, multiplier);

        // Create an inclusion oracle used to find counterexamples to hypotheses
        inclusionOracle = new MealyBFInclusionOracle<>(this.memOracle, multiplier);
    }

    /**
     * Adds a Signal Temporal Logic (STL) property to the list of properties to be verified.
     *
     * @param stl The STL property to add.
     */
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

    /**
     * Adds a collection of Signal Temporal Logic (STL) properties to the list of properties to be verified.
     *
     * @param stlCollection The collection of STL properties to add.
     */
    protected void addSTLProperties(Collection<? extends TemporalLogic<I>> stlCollection) {
        stlCollection.forEach(this::addSTLProperty);
    }

    /**
     * Removes a Signal Temporal Logic (STL) property from the list of properties to be verified.
     *
     * @param index The index of the STL property to remove.
     */
    protected void removeSTLProperty(int index) {
        this.getSTLProperties().remove(index);
        if (!initialized) {
            log.warn("STL property list is not initialized yet. This should happen only in testing.");
            return;
        }
        this.propertyOracles.remove(index);
    }

    /**
     * Removes multiple Signal Temporal Logic (STL) properties from the list of properties to be verified.
     *
     * @param indices The collection of indices corresponding to the STL properties to remove.
     */
    protected void removeSTLProperties(Collection<Integer> indices) {
        indices.stream().sorted(Comparator.reverseOrder()).forEach(this::removeSTLProperty);
    }

    /**
     * Initializes the property oracles if they have not been initialized yet.
     * <p>
     * This method is called to set up the inclusion and emptiness oracles, which are necessary for verifying properties.
     * The initialization is delayed until after the membership oracle has been set to ensure proper configuration.
     */
    /**
     * Initializes the property oracles if they have not been initialized yet.
     *
     * <p>This method is called to set up the inclusion and emptiness oracles, which are necessary for verifying properties.
     * The initialization is delayed until after the membership oracle has been set to ensure proper configuration.</p>
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

    /**
     * Checks if a given Signal Temporal Logic (STL) formula has been newly falsified.
     *
     * @param stlFormula The STL formula to check.
     * @return true if the formula has not been previously reported as falsified; otherwise, false.
     */
    public final boolean newlyFalsifiedFormula(TemporalLogic<I> stlFormula) {
        return !reportedFormulas.contains(stlFormula);
    }

    /**
     * Attempts to disprove the current list of STL formulas against the given Mealy machine.
     * <p>
     * This method checks each STL formula in the list and tries to find a counterexample that disproves it.
     * It returns:
     * <ul>
     *     <li>A counterexample for the first newly falsified STL formula, if one exists.</li>
     *     <li>A counterexample for the first falsified STL formula, if no new falsifications are found.</li>
     *     <li>null, if no counterexamples are found.</li>
     * </ul>
     * If any formulas are truly disproved, it calls {@link #notifyFalsifiedProperty(List)} with their indices.
     *
     * @param hypothesis The Mealy machine to be verified.
     * @param inputs     The alphabet of the Mealy machine's input symbols.
     * @return A query representing a counterexample if one is found; otherwise, null.
     * @see de.learnlib.oracle.equivalence.CExFirstOracle
     */
    /**
     * Attempts to disprove the current list of STL formulas against the given Mealy machine.
     *
     * <p>This method checks each STL formula in the list and tries to find a counterexample that disproves it.
     * It returns:
     * <ul>
     *     <li>A counterexample for the first newly falsified STL formula, if one exists.</li>
     *     <li>A counterexample for the first falsified STL formula, if no new falsifications are found.</li>
     *     <li>null, if no counterexamples are found.</li>
     * </ul>
     * If any formulas are truly disproved, it calls {@link #notifyFalsifiedProperty(List)} with their indices.
     *
     * @param hypothesis The Mealy machine to be verified.
     * @param inputs     The alphabet of the Mealy machine's input symbols.
     * @return A query representing a counterexample if one is found; otherwise, null.
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
     * Notifies that the STL properties at the specified indices are falsified by the currently learned model.
     * <p>
     * This method is called when one or more STL properties have been disproved. It allows for generating new adaptive formulas based on these falsifications.
     * Note: The original formulas should not be removed; instead, they can be adapted or extended.
     *
     * @param falsifiedIndices A list of indices corresponding to the falsified STL properties.
     */
    /**
     * Notifies that the STL properties at the specified indices are falsified by the currently learned model.
     *
     * <p>This method is called when one or more STL properties have been disproved. It allows for generating new adaptive formulas based on these falsifications.
     * Note: The original formulas should not be removed; instead, they can be adapted or extended.</p>
     *
     * @param falsifiedIndices A list of indices corresponding to the falsified STL properties.
     */
    protected void notifyFalsifiedProperty(List<Integer> falsifiedIndices) {
    }

    @Override
    public String toString() {
        // Map the list of STL properties to a list of strings and join them with a comma.
        return "[" + this.getSTLProperties().stream().map(TemporalLogic::toString).collect(Collectors.joining(", ")) + "]";
    }
}
