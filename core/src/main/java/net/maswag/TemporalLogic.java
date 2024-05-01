package net.maswag;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

/**
 * <p>Interface of a TemporalLogic formula.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
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
     * TODO: I do not remember the precise specification of this method.
     */
    Set<String> getAllAPs();

    void constructAtomicStrings();

    /**
     * Returns true if the formula does not contain any temporal operators.
     *
     * @return a boolean value indicating whether the formula contains any temporal operators.
     */
    boolean isNonTemporal();

    Collection<String> getAtomicStrings();

    interface STLCost extends TemporalLogic<List<Double>> {}

    interface LTLFormula extends TemporalLogic<String> {}
}
