package net.maswag.falcaun;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import de.learnlib.sul.SULMapper;
import lombok.NonNull;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.alphabet.GrowingMapAlphabet;
import net.automatalib.word.Word;

/**
 * I/O Mapper between abstract/concrete signals using InputMapper and OutputMapper.
 * <p>
 * This class implements the SULMapper interface to provide mapping between abstract
 * string-based inputs/outputs and concrete signal-based inputs/outputs. It uses
 * InputMapper and OutputMapper for the mapping operations.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class SignalAdapter implements SULMapper<String, String, List<Double>, IOSignalPiece<List<Double>>> {
    private final Map<String, List<Double>> inputMappings;
    private final List<Character> largestOutputs;
    private final List<List<Character>> abstractOutputs;
    private final List<List<Double>> concreteOutputs;

    /**
     * Constructor for SignalAdapter without SignalMapper.
     *
     * @param inputMapper  The InputMapper for mapping abstract inputs to concrete inputs.
     * @param outputMapper The OutputMapper for mapping concrete outputs to abstract outputs.
     */
    public SignalAdapter(InputMapper inputMapper, OutputMapper outputMapper) {
        // Create input mappings
        Map<String, List<Double>> tmpMapper = new HashMap<>();
        
        for (Map<Character, Double> map : inputMapper) {
            if (tmpMapper.isEmpty()) {
                // When this is the first iteration, we just copy the inputMapper of the first dimension
                for (Map.Entry<Character, Double> elem : map.entrySet()) {
                    tmpMapper.put(String.valueOf(elem.getKey()), new ArrayList<>(Collections.singletonList(elem.getValue())));
                }
            } else {
                // When this is not the first iteration, we append the new elements to the current inputMapper.
                Map<String, List<Double>> nextMapper = new HashMap<>();
                for (Map.Entry<String, List<Double>> tElem : tmpMapper.entrySet()) {
                    for (Map.Entry<Character, Double> cElem : map.entrySet()) {
                        ArrayList<Double> tmpValue = new ArrayList<>(tElem.getValue());
                        tmpValue.add(cElem.getValue());
                        nextMapper.put(tElem.getKey() + cElem.getKey(), tmpValue);
                    }
                }
                tmpMapper = nextMapper;
            }
        }
        this.inputMappings = tmpMapper;
        this.largestOutputs = outputMapper.getLargest();
        
        abstractOutputs = new ArrayList<>();
        concreteOutputs = new ArrayList<>();
        
        for (Map<Character, Double> entry : outputMapper.getOutputMapper()) {
            ArrayList<Character> cList = new ArrayList<>(entry.keySet());
            ArrayList<Double> dList = new ArrayList<>(entry.values());
            assert cList.size() == dList.size();
            abstractOutputs.add(cList);
            concreteOutputs.add(dList);
        }
    }

    /**
     * Maps an abstract input string to a concrete list of double values.
     *
     * @param s The abstract input string to map.
     * @return The concrete list of double values corresponding to the input string.
     */
    @Override
    public List<Double> mapInput(String s) {
        return (s == null) ? null : inputMappings.get(s);
    }

    /**
     * Maps a concrete IOSignalPiece to an abstract output string.
     *
     * @param concreteIO The concrete IOSignalPiece to map.
     * @return The abstract output string corresponding to the concrete output.
     */
    @Override
    public String mapOutput(IOSignalPiece<List<Double>> concreteIO) {
        // Handle empty output mapper case
        if (concreteOutputs.isEmpty()) {
            return "";
        }
        
        List<Double> concreteOutput = this.mapConcrete(concreteIO);
        StringBuilder result = new StringBuilder(concreteOutputs.size());

        if (concreteOutput.size() != this.concreteOutputs.size()) {
            throw new IllegalArgumentException(
                "Concrete output size does not match expected size: " + concreteOutput.size() + " != " + concreteOutputs.size()
            );
        }
        
        // Process each dimension of the output
        for (int i = 0; i < concreteOutput.size(); i++) {
            double cOuti = concreteOutput.get(i);

            int searchResult = Collections.binarySearch(concreteOutputs.get(i), cOuti);
            int index = searchResult >= 0 ? searchResult : ~searchResult;
            if (index >= abstractOutputs.get(i).size()) {
                result.append(this.largestOutputs.get(i));
            } else {
                result.append(abstractOutputs.get(i).get(index));
            }
        }

        return result.toString();
    }

    /**
     * Maps an abstract input word to a concrete word.
     *
     * @param abstractInput The abstract input word to map.
     * @return The concrete word corresponding to the abstract input word.
     */
    public Word<List<Double>> mapInput(@NonNull Word<String> abstractInput) {
        return Word.fromList(abstractInput.stream().map(this::mapInput).collect(Collectors.toList()));
    }

    /**
     * Maps a list of abstract input words to a list of concrete words.
     *
     * @param abstractInputs The list of abstract input words to map.
     * @return The list of concrete words corresponding to the abstract input words.
     */
    List<Word<List<Double>>> mapInputs(List<Word<String>> abstractInputs) {
        return abstractInputs.stream().map(
                word -> (word == null) ? null : Word.fromList(word.stream().map(this::mapInput).collect(Collectors.toList()))
        ).collect(Collectors.toList());
    }

    /**
     * Maps a concrete IOSignalPiece to a list of concrete output values.
     *
     * @param concreteIO The concrete IOSignalPiece to map.
     * @return The list of concrete output values.
     */
    public List<Double> mapConcrete(IOSignalPiece<List<Double>> concreteIO) {
        if (concreteIO == null || concreteIO.getOutputSignal() == null) {
            throw new IllegalArgumentException(
                "Concrete IO signal piece or its output signal cannot be null."
            );
        }

        return concreteIO.getOutputSignal();
    }

    /**
     * Constructs an abstract alphabet from the input mappings.
     *
     * @return The abstract alphabet.
     */
    Alphabet<String> constructAbstractAlphabet() {
        return new GrowingMapAlphabet<>(this.inputMappings.keySet());
    }

    /**
     * Constructs a concrete alphabet from the input mappings.
     *
     * @return The concrete alphabet.
     */
    Alphabet<List<Double>> constructConcreteAlphabet() {
        return new GrowingMapAlphabet<>(this.inputMappings.values());
    }

    public List<List<Character>> getAbstractOutputs() {
        return abstractOutputs;
    }

    public List<Character> getLargestOutputs() {
        return largestOutputs;
    }
}