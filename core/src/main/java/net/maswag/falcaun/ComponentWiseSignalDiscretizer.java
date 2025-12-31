package net.maswag.falcaun;

import java.util.List;

public interface ComponentWiseSignalDiscretizer extends SignalDiscretizer {
    /**
     * @return The largest concrete output values for each component
     */
    List<Character> getLargestOutputs();

    /**
     * @return The list of possible concrete output values for each component
     */
    List<List<Character>> getAbstractOutputs();
}
