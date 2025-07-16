package net.maswag.falcaun.parser;

import java.util.List;

import net.maswag.falcaun.IOSignalPiece;

/**
 * Interface to construct pseudo signals from concrete signals
 */
public interface SignalMapper {
    //@ requires 0 <= index < size()
    double apply(int index, IOSignalPiece<List<Double>> concreteSignal);

    //@ ensures \result >= 0
    int size();
}
