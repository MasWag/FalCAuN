package net.maswag;

import lombok.Getter;

import java.util.*;
import java.util.stream.Collectors;

@Getter
class STLAnd extends STLCost {
    private final List<STLCost> subFormulas;

    STLAnd(STLCost subFml1, STLCost subFml2) {
        this.subFormulas = Arrays.asList(subFml1, subFml2);
        this.nonTemporal = subFml1.nonTemporal && subFml2.nonTemporal;
    }

    STLAnd(List<STLCost> subFormulas) {
        this.subFormulas = subFormulas;
        this.nonTemporal = subFormulas.stream().map(STLCost::isNonTemporal).reduce((a, b) -> a && b).orElse(false);
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal signal) {
        return subFormulas.stream().map(subFml -> subFml.getRoSI(signal)).filter(
                Objects::nonNull).reduce(new RoSI(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY), RoSI::min);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return subFormulas.stream().map(STLCost::toString).collect(Collectors.joining(" && "));
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected void constructAtomicStrings() {
        if (this.nonTemporal) {
            this.atomicStrings = new HashSet<>(getAllAPs());
            for (STLCost subFml : subFormulas) {
                this.atomicStrings.retainAll(subFml.getAtomicStrings());
            }
        } else {
            this.atomicStrings = null;
        }
    }

    /** {@inheritDoc} */
    @Override
    protected Set<String> getAllAPs() {
        return subFormulas.get(0).getAllAPs();
    }

    /** {@inheritDoc} */
    @Override
    public String toAbstractString() {
        if (nonTemporal) {
            constructAtomicStrings();
            return this.atomicStrings.stream().map(
                    s -> "( output == \"" + s + "\" )").collect(Collectors.joining(" || "));
        } else {
            return this.subFormulas.stream().map(STLCost::toAbstractString).map(
                    s -> "( " + s + " )").collect(Collectors.joining(" && "));
        }
    }
}
