package net.maswag.falcaun;

import lombok.Getter;

import java.util.Set;
import java.util.stream.Collectors;

/**
 * Abstract base class for temporal logic formulas.
 *
 * This class provides a framework for implementing temporal logic formulas, which can be used to specify properties of system behavior over time.
 *
 * @param <I> The type of the input at each step.
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public abstract class AbstractTemporalLogic<I> implements TemporalLogic<I> {
    /**
     * Default constructor for AbstractTemporalLogic.
     * Initializes a new instance with default values. Subclasses should call this constructor
     * and then set appropriate values for their specific implementation.
     */
    protected AbstractTemporalLogic() {
        // Default constructor
    }
    /**
     * Indicates whether the formula is non-temporal.
     */
    @Getter
    boolean nonTemporal;
    
    /**
     * Indicates whether the formula has been initialized.
     */
    @Getter
    boolean initialized = false;
    
    /**
     * A set of atomic propositions such that the formula is satisfied if and only if one of these propositions is satisfied.
     * This field is null for temporal formulas.
     */
    Set<String> satisfyingAtomicPropositions;
    
    /**
     * The type of input/output (I/O) that the formula is concerned with, either {@link IOType#INPUT} or {@link IOType#OUTPUT}.
     */
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
     * Constructs an abstract string representation of the formula using the strings of atomic propositions.
     *
     * This method is meaningful only for non-temporal formulas that contain constraints on either inputs or outputs.
     *
     * @return The abstract string representation of the formula.
     * @throws IllegalStateException If the formula is not initialized when this method is called.
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
     * Returns the set of atomic propositions such that the formula is satisfied if and only if one of these propositions is satisfied.
     *
     * For temporal formulas, this method returns {@code null} because no such set exists.
     *
     * @return The set of satisfying atomic propositions, or {@code null} if the formula is temporal.
     */
    @Override
    public Set<String> getSatisfyingAtomicPropositions() {
        if (this.isNonTemporal() && satisfyingAtomicPropositions == null) {
            constructSatisfyingAtomicPropositions();
        }
        return satisfyingAtomicPropositions;
    }
}
