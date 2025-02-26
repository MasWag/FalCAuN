package net.maswag.falcaun;

import lombok.Getter;
import net.automatalib.word.Word;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Signal of Simulink
 */
public class Signal {
    protected double timeStep;
    protected List<List<Double>> signalValues = new ArrayList<>();
    @Getter
    protected List<Double> timestamps = new ArrayList<>();

    /**
     * Constructs a new Signal with the specified time step.
     *
     * @param timeStep the time step for the signal
     */
    public Signal(double timeStep) {
        this.timeStep = timeStep;
    }

    /**
     * Adds a new value to the signal.
     *
     * @param inputValue the value to add
     * @return true if the value was added successfully
     */
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

    /**
     * Adds all values from the specified collection to the signal.
     *
     * @param inputValues the collection of values to add
     */
    public void addAll(Collection<? extends List<Double>> inputValues) {
        for (List<Double> inputValue : inputValues) {
            this.add(inputValue);
        }
        assert this.signalValues.size() == timestamps.size();
    }

    /**
     * Adds all values from the specified word to the signal.
     *
     * @param inputValues the word of values to add
     */
    public void addAll(Word<? extends List<Double>> inputValues) {
        for (List<Double> inputValue : inputValues) {
            this.add(inputValue);
        }
        assert this.signalValues.size() == timestamps.size();
    }

    /**
     * Returns the duration of the signal.
     *
     * @return the duration of the signal
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
     * Returns the length of the signal.
     *
     * @return the length of the signal
     */
    public int size() {
        assert signalValues.size() == timestamps.size();
        return timestamps.size();
    }

    /**
     * Returns the dimension of the signal.
     *
     * @return the dimension of the signal if the input value is already set, otherwise null
     */
    public Integer dimension() {
        if (signalValues.isEmpty()) {
            return null;
        } else {
            return signalValues.get(0).size();
        }
    }

    /**
     * Clears the signal.
     */
    public void clear() {
        this.signalValues.clear();
        this.timestamps.clear();
    }

    /**
     * Returns the value of the index-th control point of the signal.
     *
     * @param index the index
     * @return the value of the index-th control point of the signal
     */
    public List<Double> get(int index) {
        return this.signalValues.get(index);
    }

    /**
     * Returns the signal values of the index-th signal.
     *
     * @param index the index
     * @return the signal values of the index-th signal
     */
    public List<Double> dimensionGet(int index) {
        List<Double> result = new ArrayList<>();
        for (List<Double> inputValue : signalValues) {
            result.add(inputValue.get(index));
        }
        return result;
    }
}
