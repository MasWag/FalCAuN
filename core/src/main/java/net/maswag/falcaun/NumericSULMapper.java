package net.maswag.falcaun;

import java.util.List;
import java.util.Map;

import de.learnlib.sul.SULMapper;
import lombok.NonNull;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.word.Word;

/**
 * I/O Mapper between abstract/concrete NumericSUL.
 * <p>
 * This class provides mapping between abstract string-based inputs/outputs and concrete signal-based inputs/outputs.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class NumericSULMapper implements SULMapper<String, String, List<Double>, IOSignalPiece<List<Double>>> {
    // Internal delegates for the new implementation
    protected final SignalAdapter signalAdapter;

    private final SignalDeriver signalDeriver;

    /**
     * <p>Constructor for NumericSULMapper.</p>
     *
     * @param inputMapper    A {@link java.util.List} of {@link java.util.Map}s
     *                       from a concrete value to the corresponding abstract alphabet.
     * @param largestOutputs A {@link java.util.List} of abstract alphabets representing
     *                       a larger values for each index of outputs.
     * @param outputMapper   A {@link java.util.List} of {@link java.util.Map}s
     *                       from an abstract alphabet to the corresponding concrete value.
     * @param sigMap         A {@link SignalMapper} object that constructs additinal values from concrete output values.
     */
    public NumericSULMapper(List<Map<Character, Double>> inputMapper,
                             List<Character> largestOutputs, List<Map<Character, Double>> outputMapper,
                             SignalMapper sigMap) {
        // Create InputMapper and OutputMapper from the provided parameters
        InputMapper inputMapperObj = InputMapper.fromMappings(inputMapper);
        OutputMapper outputMapperObj = new OutputMapper(outputMapper, largestOutputs);
        
        // Create SignalAdapter without SignalMapper
        this.signalAdapter = new SignalAdapter(inputMapperObj, outputMapperObj);
        
        // Create SignalDeriver with SignalMapper
        this.signalDeriver = new SignalDeriver(sigMap);
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

    /**
     * {@inheritDoc}
     */
    @Override
    public List<Double> mapInput(String s) {
        // Delegate to SignalAdapter
        return signalAdapter.mapInput(s);
    }

    /**
     * Maps an abstract input word to a concrete word.
     *
     * @param abstractInput The abstract input word to map.
     * @return The concrete word corresponding to the abstract input word.
     */
    public Word<List<Double>> mapInput(@NonNull Word<String> abstractInput) {
        // Delegate to SignalAdapter
        return signalAdapter.mapInput(abstractInput);
    }

    /**
     * Maps a list of abstract input words to a list of concrete words.
     *
     * @param abstractInputs The list of abstract input words to map.
     * @return The list of concrete words corresponding to the abstract input words.
     */
    public List<Word<List<Double>>> mapInputs(List<Word<String>> abstractInputs) {
        // Delegate to SignalAdapter
        return signalAdapter.mapInputs(abstractInputs);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String mapOutput(IOSignalPiece<List<Double>> concreteIO) {
        // First derive additional signals using SignalDeriver
        IOSignalPiece<List<Double>> derivedIO = signalDeriver.mapOutput(concreteIO);
        
        // Then map to abstract output using SignalAdapter
        return signalAdapter.mapOutput(derivedIO);
    }

    /**
     * Maps a concrete IOSignalPiece to a list of concrete output values.
     *
     * @param concreteIO The concrete IOSignalPiece to map.
     * @return The list of concrete output values.
     */
    public List<Double> mapConcrete(IOSignalPiece<List<Double>> concreteIO) {
        // First derive additional signals using SignalDeriver
        IOSignalPiece<List<Double>> derivedIO = signalDeriver.mapOutput(concreteIO);

        // Then map to abstract output using SignalAdapter
        return signalAdapter.mapConcrete(derivedIO);
    }

    /**
     * Constructs an abstract alphabet from the input mappings.
     *
     * @return The abstract alphabet.
     */
    public Alphabet<String> constructAbstractAlphabet() {
        // Delegate to SignalAdapter
        return signalAdapter.constructAbstractAlphabet();
    }

    /**
     * Constructs a concrete alphabet from the input mappings.
     *
     * @return The concrete alphabet.
     */
    public Alphabet<List<Double>> constructConcreteAlphabet() {
        // Delegate to SignalAdapter
        return signalAdapter.constructConcreteAlphabet();
    }
}
