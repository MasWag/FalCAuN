package net.maswag.falcaun;

import java.util.List;

/**
 * Interface to construct pseudo signals from concrete signals
 */
public interface SignalMapper {
    /**
     * Given {@literal concreteSignal}, construct {@literal index}-th signal
     * 
     * @param index is required to be 0 <= index < size()
     * @param concreteSignal
     * @return constructed concrete output
     */
    double apply(int index, IOSignalPiece<List<Double>> concreteSignal);

    /**
     * @return is ensured to be >= 0
     */
    int size();
}
