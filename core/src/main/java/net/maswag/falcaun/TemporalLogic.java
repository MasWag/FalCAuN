package net.maswag.falcaun;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

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

    /**
     * Evaluate the formula on the given signal and returns the RoSI, i.e., the range of the possible robustness values after concatenating a suffix.
     *
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
     */
    @Nullable
    Collection<String> getSatisfyingAtomicPropositions();

    interface STLCost extends TemporalLogic<List<Double>> {}

    interface LTLFormula extends TemporalLogic<String> {}
}
