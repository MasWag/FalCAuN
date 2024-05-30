package net.maswag.falcaun;

import com.google.common.collect.Streams;
import lombok.Getter;
import org.apache.commons.math3.util.Pair;

import javax.annotation.Nullable;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static java.lang.Math.ceil;

/**
 * A pair of time and values.
 *
 * @param <T> The type of the values
 */
@Getter
public class ValueWithTime<T> {
    protected final List<Double> timestamps;
    protected final List<T> values;

    ValueWithTime() {
        // Initialization with empty lists
        this.timestamps = Collections.emptyList();
        this.values = Collections.emptyList();
    }

    ValueWithTime(List<Double> timestamps, List<T> values) {
        if (timestamps.size() != values.size()) {
            throw new IllegalArgumentException("The size of timestamp and values must be the same");
        }
        this.timestamps = timestamps;
        this.values = values;
    }

    /**
     * Get the number of contained values.
     */
    public int size() {
        return timestamps.size();
    }

    /**
     * Get the value at the given time.
     */
    @Nullable
    public T at(double time) {
        assert(timestamps.size() == values.size());
        for (int i = 0; i < timestamps.size(); i++) {
            if (timestamps.get(i) == time) {
                return values.get(i);
            }
        }
        return null;
    }

    /**
     * Get the values in the given time range.
     *
     * @param from The start time (non-inclusive)
     * @param to The end time (inclusive)
     */
    public ValueWithTime<T> range(double from, double to) {
        assert(from < to);
        assert(timestamps.size() == values.size());
        return Streams.zip(timestamps.stream(), values.stream(), Pair::new)
                .filter(pair -> from < pair.getFirst() && pair.getFirst() <= to)
                .collect(Collectors.collectingAndThen(Collectors.toList(), list -> {
                    List<Double> newTimestamp = list.stream().map(Pair::getFirst).collect(Collectors.toList());
                    List<T> newValues = list.stream().map(Pair::getSecond).collect(Collectors.toList());
                    return new ValueWithTime<>(newTimestamp, newValues);
                }));
    }

    /**
     * Stream the List of values between each signal step.
     * <p>The i-th element is the list of values between (i-1) * signalStep and i * signalStep </p>
     *
     * @param signalStep The time step between each signal
     */
    public Stream<List<T>> stream(double signalStep) {
        assert(timestamps.size() == values.size());
        return Streams.zip(timestamps.stream(), values.stream(), Pair::new)
                .collect(Collectors.groupingBy(pair -> (int) ceil(pair.getFirst() / signalStep)))
                .values().stream()
                .map(list -> list.stream().map(Pair::getSecond).collect(Collectors.toList()));
    }
}
