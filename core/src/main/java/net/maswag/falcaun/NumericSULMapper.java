package net.maswag.falcaun;

import de.learnlib.sul.SULMapper;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.alphabet.GrowingMapAlphabet;
import net.automatalib.word.Word;
import lombok.NonNull;
import lombok.extern.slf4j.Slf4j;

import java.util.*;
import java.util.stream.Collectors;

/**
 * I/O Mapper between abstract/concrete NumericSUL.
 * <p>
 * TODO For now, the abstract alphabet is String for simplicity but later, it can be integers to handle more data.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class NumericSULMapper implements SULMapper<String, String, List<Double>, IOSignalPiece<List<Double>>> {
    private final Map<String, List<Double>> inputMapper;
    private final List<Character> largestOutputs;
    private final SignalMapper sigMap;

    private final List<List<Character>> abstractOutputs;
    private final List<List<Double>> concreteOutputs;

    /**
     * <p>Constructor for NumericSULMapper.</p>
     *
     * @param inputMapper    A {@link java.util.List} of {@link java.util.Map}s
     *                       from a concrete value to the corresponding abstract alphabet.
     * @param largestOutputs A {@link java.util.List} of abstract alphabets representing
     *                       a larger values for each index of outputs.
     * @param outputMapper   A {@link java.util.List} of {@link java.util.Map}s
     *                       from an abstract alphabet to the corresponding concrete value.
     * @param sigMap         A {@link SignalMapper} object that constructs additional values from concrete output values.
     */
    public NumericSULMapper(List<Map<Character, Double>> inputMapper,
                            List<Character> largestOutputs, List<Map<Character, Double>> outputMapper,
                            SignalMapper sigMap) {
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

        this.inputMapper = tmpMapper;
        this.largestOutputs = largestOutputs;

        abstractOutputs = new ArrayList<>();
        concreteOutputs = new ArrayList<>();

        for (Map<Character, Double> entry : outputMapper) {
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

            abstractOutputs.add(cList);
            concreteOutputs.add(dList);
        }
        this.sigMap = sigMap;
        log.debug("sigMap size: {}", sigMap.size());
    }

    /**
     * <p>Constructor for SimulinkSULMapper.</p>
     *
     * @param inputMapper        An input mapper.
     * @param outputMapperReader The reader of output mapper.
     * @param sigMap             An signal mapper.
     */
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
        return (s == null) ? null : inputMapper.get(s);
    }

    /**
     * Maps an abstract input word to its corresponding concrete values.
     *
     * @param abstractInput the abstract input word to be mapped
     * @return a {@link Word} of concrete values corresponding to the abstract input word
     */
    public Word<List<Double>> mapInput(@NonNull Word<String> abstractInput) {
        return Word.fromList(abstractInput.stream().map(this::mapInput).collect(Collectors.toList()));
    }

    public List<Word<List<Double>>> mapInputs(List<Word<String>> abstractInputs) {
        return abstractInputs.stream().map(
                word -> (word == null) ? null : Word.fromList(word.stream().map(this::mapInput).collect(Collectors.toList()))
        ).collect(Collectors.toList());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String mapOutput(IOSignalPiece<List<Double>> concreteIO) {
        List<Double> concreteOutput = concreteIO.getOutputSignal();
        // System.out.println("AF: " + concreteOutput.get(0));
        StringBuilder result = new StringBuilder(concreteOutputs.size());
        assert concreteOutputs.size() == sigMap.size() + concreteOutput.size();

        for (int i = 0; i < concreteOutputs.size(); i++) {
            double cOuti;
            if (i < concreteOutput.size()) {
                cOuti = concreteOutput.get(i);
            } else {
                cOuti = sigMap.apply(i - concreteOutput.size(), concreteIO);
            }
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
     * Applies {@link SignalMapper} passed to the constructor as {@code sigMap}
     * to {@code concreteIO}
     * 
     * @param concreteIO The concrete input and output signal pair
     * @return A list of concrete output values, including the original concrete output values and additional values constructed by {@code sigMap}
     */
    public List<Double> mapConcrete(IOSignalPiece<List<Double>> concreteIO) {
        List<Double> concreteOutput = concreteIO.getOutputSignal();
        List<Double> result = new ArrayList<>(concreteOutput);
        for (int i = 0; i < sigMap.size(); i++) {
            result.add(sigMap.apply(i, concreteIO));
        }
        return result;
    }

    public Alphabet<String> constructAbstractAlphabet() {
        return new GrowingMapAlphabet<>(this.inputMapper.keySet());
    }

    public Alphabet<List<Double>> constructConcreteAlphabet() {
        return new GrowingMapAlphabet<>(this.inputMapper.values());
    }
}
