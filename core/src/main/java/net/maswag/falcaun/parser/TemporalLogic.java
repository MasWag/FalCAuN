package net.maswag.falcaun.parser;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import net.maswag.falcaun.IOSignal;
import net.maswag.falcaun.LTLAPs;

/**
 * <p>Interface of a TemporalLogic formula.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 * @param <I> Type of the input at each step
 */
public interface TemporalLogic<I> extends Function<IOSignal<I>, Double> {
    /**
     * Returns a string representation of the formula in the format of <a href="https://ltsmin.utwente.nl/assets/man/ltsmin-ltl.html">LTSMin</a>.
     *
     * @return a {@link java.lang.String} object representing the formula in the format of LTSMin.
     */
    String toAbstractString();

    /**
     * Returns a string representation of the formula in the format of <a href="https://ltsmin.utwente.nl/assets/man/ltsmin-ltl.html">LTSMin</a>.
     *
     * @return a {@link java.lang.String} object representing the formula in the format of LTSMin.
     */
    default String toLTLString() {
        return this.toAbstractString();
    }

    String toOwlString();

    /**
     * Evaluate the formula on the given signal and returns the RoSI, i.e., the range of the possible robustness values after concatenating a suffix.
     *
     * @param signal The input-output signal to evaluate the formula on
     * @return a {@link RoSI} object representing the range of the possible robustness values after concatenating a suffix.
     */
    RoSI getRoSI(IOSignal<I> signal);

    /**
     * Evaluate the formula on the given signal and returns the robustness value.
     */
    default Double apply(IOSignal<I> signal) {
        return getRoSI(signal).getRobustness();
    }

    /**
     * Returns the collection of atomic propositions under consideration.
     * If this formula contains only the input constraints, the atomic propositions are the input constraints.
     * If this formula contains only the output constraints, the atomic propositions are the output constraints.
     * If this formula contains both input and output constraints, the atomic propositions are one of the input and output constraints.
     *
     * @return A set of all atomic propositions in the formula
     */
    Set<String> getAllAPs();

    default void constructSatisfyingAtomicPropositions() {
        if (!this.isInitialized()) {
            throw new IllegalStateException("The formula is not initialized but the abstract string is requested.");
        }
    }

    /**
     * Returns true if the formula does not contain any temporal operators.
     *
     * @return a boolean value indicating whether the formula contains any temporal operators.
     */
    boolean isNonTemporal();

    /**
     * Returns true if the mapper is set.
     *
     * @return true if the formula is initialized with a mapper, false otherwise
     */
    boolean isInitialized();

    /**
     * Specifies the type of the formula.
     */
    enum IOType {
        INPUT, OUTPUT, BOTH;

        /**
         * Merges two IOType.
         */
        IOType merge(IOType other) {
            if (this == other) {
                return this;
            } else {
                return BOTH;
            }
        }
    }

    @Nonnull
    IOType getIOType();

    /**
     * Returns the collection of atomic propositions such that if one of them is satisfied, the formula is satisfied.
     * If there is no such collection, returns null
     *
     * <p>Such a set exists if the formula does not contain any temporal operators.</p>
     *
     * @return A collection of atomic propositions that satisfy the formula, or null if no such collection exists
     */
    @Nullable
    Collection<String> getSatisfyingAtomicPropositions();

    TemporalLogic<I> toNnf(boolean neg);

    TemporalLogic<I> toDisjunctiveForm();

    List<TemporalLogic<I>> getAllConjunctions();

    interface STLCost extends TemporalLogic<List<Double>> {}

    interface LTLFormula extends TemporalLogic<String> {
        /**
         * Sets the universe of atomic propositions for this formula.
         * This is necessary for correctly computing negation.
         *
         * @param aps The atomic propositions containing all possible input and output APs
         */
        void setAPs(LTLAPs aps);

        /**
         * Gets the atomic propositions for this formula.
         *
         * @return The atomic propositions, or null if not set
         */
        LTLAPs getAPs();

        /**
         * Collects all atomic propositions from this formula and its subformulas.
         *
         * @param aps The atomic propositions to populate
         */
        void collectAtomicPropositions(LTLAPs aps);
    }
}
