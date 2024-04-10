package net.maswag;

import lombok.Getter;
import net.automatalib.word.Word;

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
     * <p>toAbstractString.</p>
     *
     * @return a {@link String} object.
     */
    String toAbstractString();

    String toLTLString();

    /**
     * <p>getRoSI.</p>
     *
     * @return a {@link RoSI} object.
     */
    RoSI getRoSI(IOSignal<I> signal);

    Double apply(IOSignal<I> signal);

    Set<String> getAllAPs();

    void constructAtomicStrings();

    boolean isNonTemporal();

    Collection<String> getAtomicStrings();

    interface STLCost extends TemporalLogic<List<Double>> {}

    interface LTLFormula extends TemporalLogic<String> {}
}
