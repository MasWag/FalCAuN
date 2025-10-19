package net.maswag.falcaun;

import lombok.Getter;
import net.automatalib.word.Word;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Signal is a sequence of values, each associated with an increasing timestamp.
 */
public class Signal {
    /**
     * The time step of signals.
     * When calling {@link #add(List)} or {@link #addAll(Collection)},
     * {@code timestamps} are added as {@code duration() + timeStep}.
     */
    protected double timeStep;

    @Getter
    protected List<List<Double>> signalValues = new ArrayList<>();

    /**
     * The timestamps correspond to the signal values in {@code signalValues}.
     */
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
     * The first value is added at time 0.0,
     * and the other values are added at the last timestamp + {@code timeStep}.
     *
     * @param inputValue the value to add
     * @return {@code true} if the value was added successfully
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
     * Adds all values from the specified {@link Word} to the signal.
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
     * Returns the duration of the signal, the difference between the last and first timestamps.
     * In this class, the duration is the same as the last timestamp.
     * If the signal is empty, returns 0.0.
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

    /**
     * Returns the list containing both the timestamps and the signal values.
     *
     * @return a list of lists. Each inner list contains the timestamp followed by the signal values
     */
    public List<List<Double>> asList() {
        List<List<Double>> result = new ArrayList<>();
        for (int i = 0; i < size(); i++) {
            List<Double> combinedValue = new ArrayList<>();
            combinedValue.add(timestamps.get(i));
            combinedValue.addAll(signalValues.get(i));
            result.add(combinedValue);
        }
        return result;
    }

    /**
     * Returns a new Signal whose values are linearly interpolated
     * at the given {@code newTimeStep}, writing directly into the result.
     *
     * @param newTimeStep the time step for the interpolated signal
     * @return a Signal containing the linearly interpolated data
     */
    public Signal linearInterpolate(double newTimeStep) {
        // Build result with its own timeStep
        Signal result = new Signal(newTimeStep);

        // Quick return if too few points
        if (this.size() < 2) {
            // just copy timestamps & values
            for (int i = 0; i < this.size(); i++) {
                result.timestamps.add(this.timestamps.get(i));
                result.signalValues.add(new ArrayList<>(this.signalValues.get(i)));
            }
            return result;
        }

        int cur = 0, next = 1;
        // add the very first control point
        result.timestamps.add(this.timestamps.get(0));
        result.signalValues.add(new ArrayList<>(this.signalValues.get(0)));

        while (next < this.size()) {
            double t0 = this.timestamps.get(cur);
            double t1 = this.timestamps.get(next);

            // if duplicate time, just copy forward
            if (t0 == t1) {
                result.timestamps.add(t1);
                result.signalValues.add(new ArrayList<>(this.signalValues.get(next)));
                cur++;
                next++;
                continue;
            }

            double t = t0;
            List<Double> v0 = this.signalValues.get(cur);
            List<Double> v1 = this.signalValues.get(next);
            int dim = v0.size();

            // step by newTimeStep until we hit or pass t1
            while (t + newTimeStep < t1) {
                t += newTimeStep;
                double ratio = (t - t0) / (t1 - t0);

                // build interpolated value vector
                List<Double> interpValues = new ArrayList<>(dim);
                for (int i = 0; i < dim; i++) {
                    interpValues.add(v0.get(i) + ratio * (v1.get(i) - v0.get(i)));
                }

                result.timestamps.add(t);
                result.signalValues.add(interpValues);
            }

            // finally add the exact next control point
            result.timestamps.add(t1);
            result.signalValues.add(new ArrayList<>(v1));

            cur++;
            next++;
        }

        return result;
    }
}
