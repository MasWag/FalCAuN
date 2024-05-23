package net.maswag;

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
 * Interface for potentially adaptive set of STL formulas
 *
 * @author Masaki Waga
 * @param <I> Type of the input at each step.
 * @see BlackBoxVerifier
 * @see NumericSULVerifier
 */
public interface AdaptiveSTLUpdater<I> extends InclusionOracle.MealyInclusionOracle<String, String>, BlackBoxOracle.MealyBlackBoxOracle<String, String> {
    /**
     * Returns the current list of STL formulas
     * The result may change only after the call of findCounterExample
     */
    List<TemporalLogic<I>> getSTLProperties();

    /**
     * Returns the current list of LTL formulas in the string representation
     */
    default List<String> getLTLProperties() {
        return getSTLProperties().stream().map(TemporalLogic::toLTLString).collect(Collectors.toList());
    }

    /**
     * Returns the current list of LTL formulas in MealyPropertyOracle
     */
    default List<PropertyOracle.MealyPropertyOracle<String, String, String>> list() {
        return stream().collect(Collectors.toList());
    }

    /**
     * Returns the current list of LTL formulas in MealyPropertyOracle in stream
     */
    Stream<PropertyOracle.MealyPropertyOracle<String, String, String>> stream();

    /**
     * Returns if all the properties are disproved
     */
    boolean allDisproved();

    /**
     * Returns the number of the current list of STL formulas
     */
    default int size() {
        return getSTLProperties().size();
    }

    /**
     * Reset the list of the STL formulas to the initial one.
     */
    void reset();

    /**
     * Set new membership oracle. This is necessary to call list() and stream()
     */
    void setMemOracle(@NotNull MembershipOracle.MealyMembershipOracle<String, String> memOracle);

    /**
     * Set the input alphabet we are using.
     */
    void setInputAlphabet(Alphabet<String> inputAlphabet);

    /**
     * Returns if the formula is not yet falsified
     */
    boolean newlyFalsifiedFormula(TemporalLogic<I> stlFormula);
}
