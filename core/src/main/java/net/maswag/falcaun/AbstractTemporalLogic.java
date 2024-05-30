package net.maswag.falcaun;

import lombok.Getter;

import java.util.Set;
import java.util.stream.Collectors;

/**
 * <p>Abstract TemporalLogic class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 * @param <I> Type of the input at each step
 */
@Getter
public abstract class AbstractTemporalLogic<I> implements TemporalLogic<I> {
    boolean nonTemporal;
    boolean initialized = false;
    Set<String> satisfyingAtomicPropositions;
    IOType iOType;

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        AbstractTemporalLogic<I> stlCost = (AbstractTemporalLogic<I>) o;

        return this.hashCode() == stlCost.hashCode();
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
}
