package org.group_mmm;

import java.util.List;
import java.util.function.Function;

/**
 * Class to construct pseudo signals from concrete signals
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class SignalMapper {
    final private List<Function<List<Double>, Double>> sigMap;

    public SignalMapper(List<Function<List<Double>, Double>> sigMap) {
        this.sigMap = sigMap;
    }

    //@ requires 0 <= index < size()
    double apply(int index, List<Double> concreteSignal) {
        return this.sigMap.get(index).apply(concreteSignal);
    }

    //@ ensures \result >= 0
    int size() {
        return this.sigMap.size();
    }
}
