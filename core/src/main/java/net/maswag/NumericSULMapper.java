package net.maswag;

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
public class NumericSULMapper implements SULMapper<String, String, List<Double>, IOSignalPiece> {
    private Map<String, List<Double>> inputMapper;
    private List<Character> largestOutputs;
    private SignalMapper sigMap;

    private List<List<Character>> abstractOutputs;
    private List<List<Double>> concreteOutputs;

    /**
     * <p>Constructor for SimulinkSULMapper.</p>
     *
     * @param inputMapper    a {@link java.util.List} object.
     * @param largestOutputs a {@link java.util.List} object.
     * @param outputMapper   a {@link java.util.List} object.
     * @param sigMap         a {@link java.util.List} object.
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
            ArrayList<Character> cList = new ArrayList<>(entry.keySet());
            ArrayList<Double> dList = new ArrayList<>(entry.values());
            assert cList.size() == dList.size();
            abstractOutputs.add(cList);
            concreteOutputs.add(dList);
        }
        this.sigMap = sigMap;
        log.debug("sigMap size: " + sigMap.size());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public List<Double> mapInput(String s) {
        return (s == null) ? null : inputMapper.get(s);
    }

    public Word<List<Double>> mapInput(@NonNull Word<String> abstractInput) {
        return Word.fromList(abstractInput.stream().map(this::mapInput).collect(Collectors.toList()));
    }

    List<Word<List<Double>>> mapInputs(List<Word<String>> abstractInputs) {
        return abstractInputs.stream().map(
                word -> (word == null) ? null : Word.fromList(word.stream().map(this::mapInput).collect(Collectors.toList()))
        ).collect(Collectors.toList());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String mapOutput(IOSignalPiece concreteIO) {
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

    public List<Double> mapConcrete(IOSignalPiece concreteIO) {
        List<Double> concreteOutput = concreteIO.getOutputSignal();
        List<Double> result = new ArrayList<>(concreteOutput);
        for (int i = 0; i < sigMap.size(); i++) {
            result.add(sigMap.apply(i, concreteIO));
        }
        return result;
    }

    Alphabet<String> constructAbstractAlphabet() {
        return new GrowingMapAlphabet<>(this.inputMapper.keySet());
    }

    Alphabet<List<Double>> constructConcreteAlphabet() {
        return new GrowingMapAlphabet<>(this.inputMapper.values());
    }
}
