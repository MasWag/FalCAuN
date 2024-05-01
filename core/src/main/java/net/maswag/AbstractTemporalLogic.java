package net.maswag;

import lombok.Getter;

import java.util.Set;

/**
 * <p>Abstract TemporalLogic class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Getter
public abstract class AbstractTemporalLogic<I> implements TemporalLogic<I> {
    boolean nonTemporal;
    Set<String> atomicStrings;

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
}
