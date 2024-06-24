package net.maswag.falcaun;

import lombok.Getter;

import java.util.Set;
import java.util.stream.Collectors;

/**
 * <p>Abstract TemporalLogic class.</p>
 *
 * @param <I> Type of the input at each step
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public abstract class AbstractTemporalLogic<I> implements TemporalLogic<I> {
    @Getter
    boolean nonTemporal;
    @Getter
    boolean initialized = false;
    Set<String> satisfyingAtomicPropositions;
    @Getter
    IOType iOType;

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        return this.hashCode() == o.hashCode();
    }

    @Override
    public int hashCode() {
        // Hash code is implemented based on the string representation.
        return this.toString().hashCode();
    }

    /**
     * Construct the abstract string using the strings on the atomic propositions.
     * This method makes sense only if the formula is non-temporal and contains the constraints only on inputs or outputs.
     */
    protected String makeAbstractStringWithAtomicStrings() {
        if (!this.isInitialized()) {
            throw new IllegalStateException("The formula is not initialized but the abstract string is requested.");
        }
        if (this.satisfyingAtomicPropositions == null) {
            constructSatisfyingAtomicPropositions();
        }
        if (this.iOType == IOType.INPUT)
            return this.satisfyingAtomicPropositions.stream().map(
                    s -> "( input == \"" + s + "\" )").collect(Collectors.joining(" || "));
        else {
            return this.satisfyingAtomicPropositions.stream().map(
                    s -> "( output == \"" + s + "\" )").collect(Collectors.joining(" || "));
        }
    }

    /**
     * It returns the set of atomic propositions such that the formula is satisfied if and only if one of the atomic propositions in the returned set is satisfied.
     * Since such a set does not exist for temporal formulas, it returns null for such formulas.
     */
    @Override
    public Set<String> getSatisfyingAtomicPropositions() {
        if (this.isNonTemporal() && satisfyingAtomicPropositions == null) {
            constructSatisfyingAtomicPropositions();
        }
        return satisfyingAtomicPropositions;
    }
}
