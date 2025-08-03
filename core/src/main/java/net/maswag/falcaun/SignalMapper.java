package net.maswag.falcaun;

import java.util.List;

/**
 * Interface to construct pseudo signals from concrete signals
 */
public interface SignalMapper {
    /**
     * Given {@literal concreteSignal}, construct {@literal index}-th signal
     * 
     * @param index The index of the signal to apply the mapper. It is required to be {@literal 0 <= index < size()}
     * @param concreteSignal
     * @return The constructed concrete output value
     */
    double apply(int index, IOSignalPiece<List<Double>> concreteSignal);

    /**
     * @return The size of the mapper, i.e. the number of signals it can map.
     *         It is ensured to be {@literal >= 0}
     */
    int size();
}
