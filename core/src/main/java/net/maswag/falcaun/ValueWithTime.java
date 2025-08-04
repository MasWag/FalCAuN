package net.maswag.falcaun;

import com.google.common.collect.Streams;
import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import org.apache.commons.math3.util.Pair;

import javax.annotation.Nullable;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static java.lang.Math.ceil;

/**
 * A sequence of values each associated with an increasing timestamp.
 *
 * @param <T> the type of values
 */
@Slf4j
@Getter
public class ValueWithTime<T> {
    protected final List<Double> timestamps;
    protected final List<T> values;

    /**
     * Initialization with empty lists
     */
    public ValueWithTime() {
        this.timestamps = Collections.emptyList();
        this.values = Collections.emptyList();
    }

    /**
     * Initialization with given timestamps and values.
     *
     * i-th timestamp corresponds to i-th value.
     * So the sizes of timestamps and values must be equal.
     *
     * @param timestamps The list of timestamps
     * @param values The list of values
     * @throws IllegalArgumentException If the sizes of timestamps and values are not equal or if any value is null
     */
    public ValueWithTime(List<Double> timestamps, List<T> values) {
        if (timestamps.size() != values.size()) {
            throw new IllegalArgumentException("The size of timestamp and values must be the same");
        }
        // Throws an exception if any of the value is null
        if (values.stream().anyMatch(Objects::isNull)) {
            throw new IllegalArgumentException("The values must not be null");
        }

        this.timestamps = timestamps;
        this.values = values;
    }

    /**
     * Get the duration of the signal.
     * That is the difference between the last and first timestamps.
     *
     * @return The duration of the signal, or 0 if the signal is empty
     */
    public double duration() {
        if (timestamps.isEmpty()) {
            return 0.0;
        } else {
            return timestamps.get(timestamps.size() - 1) - timestamps.get(0);
        }
    }

    /**
     * Get the number of contained values.
     */
    public int size() {
        return timestamps.size();
    }

    /**
     * Check if the value is empty.
     */
    public boolean isEmpty() {
        return timestamps.isEmpty();
    }

    /**
     * Get the value at the given time.
     *
     * @param time The time to get the value at
     * @return the value at the closest time
     */
    @Nullable
    public T at(double time) {
        assert(timestamps.size() == values.size());
        Double best = null;
        double bestTime = 0;
        for (int i = 0; i < timestamps.size(); i++) {
            best = timestamps.get(i);
            bestTime = Math.max(time, bestTime);
            if (timestamps.get(i) == time) {
                return values.get(i);
            }
            if (timestamps.get(i) > time) {
                if (time - bestTime < timestamps.get(i) - time) {
                    log.info("Failed to find the exact time. Using the value at the closest time: {}", best);
                    return values.get(i - 1);
                } else {
                    log.info("Found the exact time. Using the value at the closest time: {}", this.timestamps.get(i));
                    return values.get(i);
                }
            }
        }
        log.info("Failed to find the exact time. Using the value at the closest time: {}", best);
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
        return this.range(from, to, false, true);
    }

    /**
     * Get the values in the given time range.
     *
     * @param from The start time
     * @param to The end time
     * @param leftInclusive Whether the start time is inclusive
     * @param rightInclusive Whether the end time is inclusive
     */
    public ValueWithTime<T> range(double from, double to, boolean leftInclusive, boolean rightInclusive) {
        assert(from <= to);
        assert(timestamps.size() == values.size());
        return Streams.zip(timestamps.stream(), values.stream(), Pair::new)
                .filter(pair -> {
                    double timestamp = pair.getFirst();
                    boolean validStart = leftInclusive ? (from <= timestamp) : (from < timestamp);
                    boolean validEnd = rightInclusive ? (timestamp <= to) : (timestamp < to);
                    return validStart && validEnd;
                })
                .collect(Collectors.collectingAndThen(Collectors.toList(), list -> {
                    List<Double> newTimestamp = list.stream().map(Pair::getFirst).collect(Collectors.toList());
                    List<T> newValues = list.stream().map(Pair::getSecond).collect(Collectors.toList());
                    return new ValueWithTime<>(newTimestamp, newValues);
                }));
    }

    /**
     * Stream the List of values between each signal step.
     * Since the values between each signal step can be multiple in general,
     * each element of the stream is a list.
     *
     * <p>The i-th element is the list of values whose timestamp is
     * between {@literal ((i-1) * signalStep, i * signalStep]}. </p>
     * @param signalStep The time step between each signal
     * @return A stream of lists of values, grouped by signal step.
     */
    public Stream<List<T>> stream(double signalStep) {
        assert(timestamps.size() == values.size());
        return Streams.zip(timestamps.stream(), values.stream(), Pair::new)
                .collect(Collectors.groupingBy(pair -> (int) ceil(pair.getFirst() / signalStep)))
                .values().stream()
                .map(list -> list.stream().map(Pair::getSecond).collect(Collectors.toList()));
    }
}
