package org.group_mmm;

import net.automatalib.words.Word;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Signal of Simulink
 */
public class Signal {
    protected double timeStep;
    protected List<List<Double>> signalValues = new ArrayList<>();
    protected List<Double> timestamps = new ArrayList<>();

    Signal(double timeStep) {
        this.timeStep = timeStep;
    }

    public boolean add(List<Double> inputValue) {
        if (this.timestamps.isEmpty()) {
            this.timestamps.add(0.0);
        } else {
            this.timestamps.add(this.duration() + timeStep);
        }
        this.signalValues.add(inputValue);
        assert signalValues.size() == timestamps.size();
        return true;
    }

    public void addAll(Collection<? extends List<Double>> inputValues) {
        for (List<Double> inputValue : inputValues) {
            this.add(inputValue);
        }
        assert this.signalValues.size() == timestamps.size();
    }

    public void addAll(Word<? extends List<Double>> inputValues) {
        for (List<Double> inputValue : inputValues) {
            this.add(inputValue);
        }
        assert this.signalValues.size() == timestamps.size();
    }

    /**
     * Returns the duration of the signal
     */
    public double duration() {
        if (this.timestamps.isEmpty()) {
            return 0.0;
        } else {
            return this.timestamps.get(this.timestamps.size() - 1);
        }
    }

    @Override
    public String toString() {
        assert signalValues.size() == timestamps.size();
        StringBuilder builder = new StringBuilder();
        builder.append('[');
        for (int i = 0; i < size(); i++) {
            builder.append(timestamps.get(i));
            for (Double value : signalValues.get(i)) {
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

    /**
     * Return the length of the signal
     */
    public int size() {
        assert signalValues.size() == timestamps.size();
        return timestamps.size();
    }

    /**
     * Return the dimension of the signal
     *
     * @return It returns the dimension of the signal if the input value is already set. Otherwise, it returns null.
     */
    public Integer dimension() {
        if (signalValues.isEmpty()) {
            return null;
        } else {
            return signalValues.get(0).size();
        }
    }

    /**
     * Clear the signal
     */
    public void clear() {
        this.signalValues.clear();
        this.timestamps.clear();
    }

    /**
     * Return the value of the index-th control point of the signal
     *
     * @param index The index
     * @return It returns the value of the index-th control point of the signal.
     */
    public List<Double> get(int index) {
        return this.signalValues.get(index);
    }

    /**
     * Return the signal values of the index-th signal
     *
     * @param index The index
     * @return It returns the signal values of the index-th signal.
     */
    public List<Double> dimensionGet(int index) {
        List<Double> result = new ArrayList<>();
        for (List<Double> inputValue : signalValues) {
            result.add(inputValue.get(index));
        }
        return result;
    }
}
