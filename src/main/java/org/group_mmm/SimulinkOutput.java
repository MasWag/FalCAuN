package org.group_mmm;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Map;

public class SimulinkOutput {

    private ArrayList<ArrayList<Character>> abstractOutputs;
    private ArrayList<ArrayList<Double>> concreteOutputs;

    private ArrayList<Double> value;
    private ArrayList<Character> largest;

    SimulinkOutput(ArrayList<Character> largest, ArrayList<Map<Character, Double>> outputMapper, ArrayList<Double> value) {
        assert outputMapper.size() == value.size();
        assert outputMapper.size() == largest.size();
        abstractOutputs = new ArrayList<>();
        concreteOutputs = new ArrayList<>();

        for (Map<Character, Double> entry : outputMapper) {
            ArrayList<Character> cList = new ArrayList<>(entry.keySet());
            ArrayList<Double> dList = new ArrayList<>(entry.values());
            assert cList.size() == dList.size();
            abstractOutputs.add(cList);
            concreteOutputs.add(dList);
        }

        this.value = value;
        this.largest = largest;
    }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder(value.size());

        for (int i = 0; i < value.size(); i++) {
            int searchResult = Collections.binarySearch(concreteOutputs.get(i), value.get(i));
            int index = searchResult >= 0 ? searchResult : ~searchResult;
            if (index >= abstractOutputs.get(i).size()) {
                result.append(this.largest.get(i));
            } else {
                result.append(abstractOutputs.get(i).get(index));
            }
        }
        return result.toString();
    }

    ArrayList<Double> toArrayList() {
        return value;
    }
}
