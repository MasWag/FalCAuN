package net.maswag.falcaun;

import java.util.List;

/**
 * Interface to construct pseudo signals from concrete signals
 */
public interface SignalMapper {
    //@ requires 0 <= index < size()
    double apply(int index, IOSignalPiece<List<Double>> concreteSignal);

    //@ ensures \result >= 0
    int size();
}
