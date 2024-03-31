package net.maswag;

import de.learnlib.oracle.BlackBoxOracle;
import de.learnlib.oracle.InclusionOracle;
import de.learnlib.oracle.MembershipOracle;
import de.learnlib.oracle.PropertyOracle;
import net.automatalib.alphabet.Alphabet;
import org.jetbrains.annotations.NotNull;

import java.util.List;
import java.util.stream.Stream;

/**
 * Interface for potentially adaptive set of STL formulas
 *
 * @author Masaki Waga
 * @see BlackBoxVerifier
 * @see NumericSULVerifier
 */
public interface AdaptiveSTLUpdater extends InclusionOracle.MealyInclusionOracle<String, String>, BlackBoxOracle.MealyBlackBoxOracle<String, String> {
    /**
     * Returns the current list of STL formulas
     * The result may change only after the call of findCounterExample
     */
    List<STLCost> getSTLProperties();

    /**
     * Returns the current list of LTL formulas in the string representation
     */
    List<String> getLTLProperties();

    /**
     * Returns the current list of LTL formulas in MealyPropertyOracle
     */
    List<PropertyOracle.MealyPropertyOracle<String, String, String>> list();

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
    int size();

    /**
     * Reset the list of the STL formulas to the initial one.
     */
    void reset();

    /**
     * Set new membership oracle. This is necessary to call list() and stream()
     */
    void setMemOracle(@NotNull MembershipOracle.MealyMembershipOracle<String, String> memOracle);

    void setInputAlphabet(Alphabet<String> inputAlphabet);

    /**
     * Returns if the formula is not yet falsified
     */
    boolean newlyFalsifiedFormula(STLCost stlFormula);
}
