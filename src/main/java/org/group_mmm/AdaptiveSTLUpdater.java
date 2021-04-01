package org.group_mmm;

import de.learnlib.api.oracle.BlackBoxOracle;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.oracle.PropertyOracle;
import net.automatalib.words.Alphabet;
import org.jetbrains.annotations.NotNull;

import java.util.List;
import java.util.stream.Stream;

/**
 * Interface for potentially adaptive set of STL formulas
 *
 * @author Masaki Waga
 * @see BlackBoxVerifier
 * @see SimulinkVerifier
 */
public interface AdaptiveSTLUpdater extends BlackBoxOracle.MealyBlackBoxOracle<String, String> {
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
     * Returns the number of the current list of STL formulas
     */
    int size();

    /**
     * Set new membership oracle. This is necessary to call list() and stream()
     */
    void setMemOracle(@NotNull MembershipOracle.MealyMembershipOracle<String, String> memOracle);

    void setInputAlphabet(Alphabet<String> inputAlphabet);
}
