package net.maswag.falcaun;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.alphabet.GrowingMapAlphabet;


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
public class SignalAdapter implements ComponentWiseSignalDiscretizer {
    private final Map<String, List<Double>> inputMappings;
    @Getter
    private final List<Character> largestOutputs;
    @Getter
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
            ArrayList<Character> cList = new ArrayList<>();
            ArrayList<Double> dList = new ArrayList<>();

            // Sort the entry by value and add keys and values to cList and dList in sorted order
            entry.entrySet()
                    .stream()
                    .sorted(Map.Entry.comparingByValue())
                    .forEachOrdered(e -> {
                        cList.add(e.getKey());
                        dList.add(e.getValue());
                    });

            assert cList.size() == dList.size();
            abstractOutputs.add(cList);
            concreteOutputs.add(dList);
        }
    }

    @Override
    public List<Double> mapInput(String s) {
        return (s == null) ? null : inputMappings.get(s);
    }

    @Override
    public String mapOutput(IOSignalPiece<List<Double>> concreteIO) {
        // Handle empty output mapper case
        if (concreteOutputs.isEmpty()) {
            return "";
        }

        List<Double> concreteOutput = this.mapConcrete(concreteIO);

        if (concreteOutput.size() != this.concreteOutputs.size()) {
            throw new IllegalArgumentException(
                    "Concrete output size does not match expected size: " + concreteOutput.size() + " != " + concreteOutputs.size()
            );
        }
        StringBuilder result = new StringBuilder(concreteOutputs.size());

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

    @Override
    public Alphabet<String> constructAbstractAlphabet() {
        return new GrowingMapAlphabet<>(this.inputMappings.keySet());
    }

    @Override
    public Alphabet<List<Double>> constructConcreteAlphabet() {
        return new GrowingMapAlphabet<>(this.inputMappings.values());
    }
}