package net.maswag.falcaun;

import java.util.List;
import java.util.Map;

import lombok.extern.slf4j.Slf4j;

/**
 * I/O Mapper between abstract/concrete NumericSUL.
 * <p>
 * This class provides mapping between abstract string-based inputs/outputs and concrete signal-based inputs/outputs.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class NumericSULMapper extends PreComposedSignalDiscretizer{

    /**
     * <p>Constructor for NumericSULMapper.</p>
     *
     * @param inputMapper    A {@link java.util.List} of {@link java.util.Map}s
     *                       from a concrete value to the corresponding abstract alphabet.
     * @param largestOutputs A {@link java.util.List} of abstract alphabets representing
     *                       a larger value for each output index.
     * @param outputMapper   A {@link java.util.List} of {@link java.util.Map}s
     *                       from an abstract alphabet to the corresponding concrete value.
     * @param sigMap         A {@link SignalMapper} object that constructs additional values from concrete output values.
     */
    public NumericSULMapper(List<Map<Character, Double>> inputMapper,
                             List<Character> largestOutputs, List<Map<Character, Double>> outputMapper,
                             SignalMapper sigMap) {
        super(new SignalAdapter(InputMapper.fromMappings(inputMapper), new OutputMapper(outputMapper, largestOutputs)), new SignalDeriver(sigMap));
    }

    /**
     * <p>Constructor for NumericSULMapper.</p>
     *
     * @param inputMapper        An input mapper.
     * @param outputMapper The reader of output mapper.
     * @param sigMap             An signal mapper.
     */
    public NumericSULMapper(List<Map<Character, Double>> inputMapper,
                            OutputMapper outputMapper,
                            SignalMapper sigMap) {
        this(inputMapper, outputMapper.getLargest(), outputMapper.getOutputMapper(), sigMap);
    }

    /**
     * <p>Constructor for NumericSULMapper.</p>
     *
     * @param inputMapper        An input mapper.
     * @param outputMapperReader The reader of output mapper.
     * @param sigMap             An signal mapper.
     * @deprecated Use {@link NumericSULMapper} with {@link InputMapper} and {@link OutputMapper} instead.
     */
    @Deprecated
    public NumericSULMapper(List<Map<Character, Double>> inputMapper,
                             OutputMapperReader outputMapperReader,
                             SignalMapper sigMap) {
        this(inputMapper, outputMapperReader.getLargest(), outputMapperReader.getOutputMapper(), sigMap);
    }
}
