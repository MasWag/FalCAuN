package org.group_mmm;

import de.learnlib.mapper.api.SULMapper;
import net.automatalib.words.Alphabet;
import net.automatalib.words.impl.SimpleAlphabet;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * I/O Mapper between abstract/concrete Simulink model.
 *
 * TODO For now, the abstract alphabet is String for simplicity but later, it can be integers to handle more data.
 */
public class SimulinkSULMapper implements SULMapper<String, String, ArrayList<Double>, ArrayList<Double>> {
    private Map<String, ArrayList<Double>> inputMapper;
    private ArrayList<Character> largestOutputs;
    private ArrayList<Function<ArrayList<Double>, Double>> sigMap;

    private ArrayList<ArrayList<Character>> abstractOutputs;
    private ArrayList<ArrayList<Double>> concreteOutputs;

    SimulinkSULMapper(ArrayList<Map<Character, Double>> inputMapper,
                      ArrayList<Character> largestOutputs, ArrayList<Map<Character, Double>> outputMapper, ArrayList<Function<ArrayList<Double>, Double>> sigMap) {
        Map<String, ArrayList<Double>> tmpMapper = new HashMap<>();

        for (Map<Character, Double> map : inputMapper) {
            if (tmpMapper.isEmpty()) {
                // When this is the first iteration, we just copy the inputMapper of the first dimension
                for (Map.Entry<Character, Double> elem : map.entrySet()) {
                    tmpMapper.put(String.valueOf(elem.getKey()), new ArrayList<>(Collections.singletonList(elem.getValue())));
                }
            } else {
                // When this is not the first iteration, we append the new elements to the current inputMapper.
                Map<String, ArrayList<Double>> nextMapper = new HashMap<>();
                for (Map.Entry<String, ArrayList<Double>> tElem : tmpMapper.entrySet()) {
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
    }

    @Override
    public ArrayList<Double> mapInput(String s) {
        return inputMapper.get(s);
    }

    @Override
    public String mapOutput(ArrayList<Double> concreteOutput) {
        // System.out.println("AF: " + concreteOutput.get(0));
        StringBuilder result = new StringBuilder(concreteOutput.size());

        for (int i = 0; i < concreteOutputs.size(); i++) {
            double cOuti;
            if (i < concreteOutput.size()) {
                cOuti = concreteOutput.get(i);
            } else {
                cOuti = sigMap.get(i - concreteOutput.size()).apply(concreteOutput);
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

    Alphabet<String> constructAbstractAlphabet() {
        return new SimpleAlphabet<>(this.inputMapper.keySet());
    }

    Alphabet<ArrayList<Double>> constructConcreteAlphabet() {
        return new SimpleAlphabet<>(this.inputMapper.values());
    }
}
