package net.maswag.falcaun;

import de.learnlib.oracle.BlackBoxOracle;
import de.learnlib.oracle.InclusionOracle;
import de.learnlib.oracle.MembershipOracle;
import de.learnlib.oracle.PropertyOracle;
import net.automatalib.alphabet.Alphabet;
import org.jetbrains.annotations.NotNull;

import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Interface for a potentially adaptive set of Signal Temporal Logic (STL) formulas.
 * This is primarily for strengthening of STL formulas presented in "Efficient Black-Box Checking via Model Checking with Strengthened Specifications" by Shijubo et al.
 * <p>
 * This interface defines methods to manage and query a set of STL formulas that can adapt over time based on new information or counterexamples.
 * 
 * It extends both {@link InclusionOracle.MealyInclusionOracle} and {@link BlackBoxOracle.MealyBlackBoxOracle}.
 *
 * @param <I> The type of the input at each step.
 * @author Masaki Waga
 * @see BlackBoxVerifier
 * @see NumericSULVerifier
 */
public interface AdaptiveSTLUpdater<I> extends InclusionOracle.MealyInclusionOracle<String, String>, BlackBoxOracle.MealyBlackBoxOracle<String, String> {
    /**
     * Returns the current list of Signal Temporal Logic (STL) formulas.
     *
     * The returned list may be updated only after a call to {@link #findCounterExample}.
     *
     * @return A list of STL properties
     */
    List<TemporalLogic<I>> getSTLProperties();

    /**
     * Returns the current list of Linear Temporal Logic (LTL) formulas in their string representations in <a href="https://ltsmin.utwente.nl/assets/man/ltsmin-ltl.html">LTSMin's syntax</a>.
     *
     * @return A list of LTL properties as strings
     */
    default List<String> getLTLProperties() {
        return getSTLProperties().stream().map(TemporalLogic::toLTLString).collect(Collectors.toList());
    }

    /**
     * Returns the current list of Linear Temporal Logic (LTL) formulas as {@link PropertyOracle.MealyPropertyOracle} instances.
     *
     * @return A list of LTL properties as MealyPropertyOracle instances
     */
    default List<PropertyOracle.MealyPropertyOracle<String, String, String>> list() {
        return stream().collect(Collectors.toList());
    }

    /**
     * Returns a stream of Linear Temporal Logic (LTL) formulas as {@link PropertyOracle.MealyPropertyOracle} instances.
     *
     * @return A stream of LTL properties as MealyPropertyOracle instances
     */
    Stream<PropertyOracle.MealyPropertyOracle<String, String, String>> stream();

    /**
     * Checks if all the Signal Temporal Logic (STL) properties have been disproved.
     *
     * @return {@code true} if all STL properties have been disproved, otherwise {@code false}.
     */
    boolean allDisproved();

    /**
     * Returns the number of Signal Temporal Logic (STL) formulas in the current list.
     *
     * @return The number of STL formulas.
     */
    default int size() {
        return getSTLProperties().size();
    }

    /**
     * Resets the list of Signal Temporal Logic (STL) formulas to their initial state.
     */
    void reset();

    /**
     * Sets a new membership oracle.
     *
     * This method must be called before invoking {@link #list()} or {@link #stream()}.
     *
     * @param memOracle The new membership oracle to set.
     */
    void setMemOracle(@NotNull MembershipOracle.MealyMembershipOracle<String, String> memOracle);

    /**
     * Sets the input alphabet used for the verification process.
     *
     * @param inputAlphabet The input alphabet to set.
     */
    void setInputAlphabet(Alphabet<String> inputAlphabet);

    /**
     * Checks if a given Signal Temporal Logic (STL) formula has not yet been falsified.
     *
     * @param stlFormula The STL formula to check.
     * @return {@code true} if the formula has not been falsified, otherwise {@code false}.
     */
    boolean newlyFalsifiedFormula(TemporalLogic<I> stlFormula);
}
