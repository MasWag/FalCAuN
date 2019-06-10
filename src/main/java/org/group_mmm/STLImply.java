package org.group_mmm;

import net.automatalib.words.Word;

import java.util.ArrayList;

public class STLImply extends STLCost {
    private STLCost subFml1, subFml2;

    STLImply(STLCost subFml1, STLCost subFml2) {
        this.subFml1 = subFml1;
        this.subFml2 = subFml2;
    }

    @Override
    public Double apply(Word<ArrayList<Double>> signal) {
        return Math.max(-subFml1.apply(signal), subFml2.apply(signal));
    }
}

