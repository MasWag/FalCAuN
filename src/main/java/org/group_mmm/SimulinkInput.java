package org.group_mmm;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

public class SimulinkInput {
    private Map<String, ArrayList<Double>> inputMapper;
    private String value;

    SimulinkInput(ArrayList<Map<Character, Double>> inputMapper, String value) {
        assert inputMapper.size() == value.length();
        Map<String, ArrayList<Double>> tmpMapper = new HashMap<>();

        for (Map<Character, Double> map : inputMapper) {
            if (tmpMapper.isEmpty()) {
                // When this is the first iteration, we just copy the mapper of the first dimension
                for (Map.Entry<Character, Double> elem : map.entrySet()) {
                    tmpMapper.put(String.valueOf(elem.getKey()), new ArrayList<>(Collections.singletonList(elem.getValue())));
                }
            } else {
                // When this is not the first iteration, we append the new elements to the current mapper.
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
        this.value = value;
    }

    @Override
    public String toString() {
        return value;
    }

    ArrayList<Double> toArrayList() {
        return inputMapper.get(value);
    }
}
