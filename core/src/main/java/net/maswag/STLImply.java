package net.maswag;

import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * <p>STLImply class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class STLImply extends STLCost {
    private STLCost subFml1, subFml2;

    STLImply(STLCost subFml1, STLCost subFml2) {
        this.subFml1 = subFml1;
        this.subFml2 = subFml2;
        this.nonTemporal = subFml1.nonTemporal && subFml2.nonTemporal;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal signal) {
        return subFml1.getRoSI(signal).assignNegate().assignMax(subFml2.getRoSI(signal));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void constructAtomicStrings() {
        if (this.nonTemporal) {
            if (this.atomicStrings == null) {
                this.atomicStrings = new HashSet<>(getAllAPs());
                this.atomicStrings.removeAll(subFml1.getAtomicStrings());
                this.atomicStrings.addAll(subFml2.getAtomicStrings());
            }
        } else {
            this.atomicStrings = null;
        }
    }

    /** {@inheritDoc} */
    @Override
    protected Set<String> getAllAPs() {
        return subFml1.getAllAPs();
    }

    /** {@inheritDoc} */
    @Override
    public String toAbstractString() {
        if (nonTemporal) {
            constructAtomicStrings();
            return this.atomicStrings.stream().map(
                    s -> "( output == \"" + s + "\" )").collect(Collectors.joining(" || "));
        } else {
            return String.format("( %s ) -> ( %s )", subFml1.toAbstractString(), subFml2.toAbstractString());
        }
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return String.format("( %s ) -> ( %s )", subFml1.toString(), subFml2.toString());
    }
}

