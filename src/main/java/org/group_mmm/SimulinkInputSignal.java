package org.group_mmm;

import net.automatalib.words.Word;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class SimulinkInputSignal {
    protected double timeStep;
    protected List<List<Double>> inputValues = new ArrayList<>();
    protected List<Double> timestamps = new ArrayList<>();

    SimulinkInputSignal(double timeStep) {
        this.timeStep = timeStep;
    }

    public boolean add(List<Double> inputValue) {
        if (inputValues.isEmpty()) {
            this.timestamps.add(0.0);
            this.inputValues.add(inputValue);
        }
        this.timestamps.add(this.duration() + timeStep);
        this.inputValues.add(inputValue);
        assert inputValues.size() == timestamps.size();
        return true;
    }

    public void addAll(Collection<? extends List<Double>> inputValues) {
        for (List<Double> inputValue : inputValues) {
            this.add(inputValue);
        }
        assert this.inputValues.size() == timestamps.size();
    }

    public void addAll(Word<? extends List<Double>> inputValues) {
        for (List<Double> inputValue : inputValues) {
            this.add(inputValue);
        }
        assert this.inputValues.size() == timestamps.size();
    }

    public double duration() {
        if (this.timestamps.isEmpty()) {
            return 0.0;
        } else {
            return this.timestamps.get(this.timestamps.size() - 1);
        }
    }

    @Override
    public String toString() {
        assert inputValues.size() == timestamps.size();
        StringBuilder builder = new StringBuilder();
        builder.append('[');
        for (int i = 0; i < size(); i++) {
            builder.append(timestamps.get(i));
            for (Double value : inputValues.get(i)) {
                builder.append(' ');
                builder.append(value);
            }
            if (i + 1 < size()) {
                builder.append("; ");
            }
        }
        builder.append(']');
        return builder.toString();
    }

    public int size() {
        assert inputValues.size() == timestamps.size();
        return timestamps.size();
    }

    public Integer dimension() {
        if (inputValues.isEmpty()) {
            return null;
        } else {
            return inputValues.get(0).size();
        }
    }

    public void clear() {
        this.inputValues.clear();
        this.timestamps.clear();
    }

    public List<Double> get(int index) {
        return this.inputValues.get(index);
    }

    public List<Double> dimensionGet(int index) {
        List<Double> result = new ArrayList<>();
        for (List<Double> inputValue : inputValues) {
            result.add(inputValue.get(index));
        }
        return result;
    }
}
