package org.group_mmm;

import net.automatalib.words.Word;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

public class STLImply extends STLCost {
    private STLCost subFml1, subFml2;

    STLImply(STLCost subFml1, STLCost subFml2) {
        this.subFml1 = subFml1;
        this.subFml2 = subFml2;
        this.nonTemporal = subFml1.nonTemporal && subFml2.nonTemporal;
    }

    @Override
    public Double apply(Word<ArrayList<Double>> signal) {
        return Math.max(-subFml1.apply(signal), subFml2.apply(signal));
    }

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

    @Override
    protected Set<String> getAllAPs() {
        return subFml1.getAllAPs();
    }

    @Override
    String toAbstractString() {
        if (nonTemporal) {
            constructAtomicStrings();
            return this.atomicStrings.stream().map(
                    s -> "( " + s + " )").collect(Collectors.joining(" || "));
        } else {
            return String.format("( %s ) -> ( %s )", subFml1.toAbstractString(), subFml2.toAbstractString());
        }
    }

    @Override
    public String toString() {
        return String.format("( %s ) -> ( %s )", subFml1.toString(), subFml2.toString());
    }
}

