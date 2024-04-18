package net.maswag;

import com.google.common.collect.Streams;
import lombok.Getter;
import org.apache.commons.math3.util.Pair;

import javax.annotation.Nullable;
import java.util.List;
import java.util.stream.Collectors;

/**
 * A pair of time and values.
 *
 * @param <T> The type of the values
 */
@Getter
public class ValueWithTime<T> {
    List<Double> timestamp;
    List<T> values;

    ValueWithTime(List<Double> timestamp, List<T> values) {
        if (timestamp.size() != values.size()) {
            throw new IllegalArgumentException("The size of timestamp and values must be the same");
        }
        this.timestamp = timestamp;
        this.values = values;
    }

    /**
     * Get the value at the given time.
     */
    @Nullable
    public T at(double time) {
        assert(timestamp.size() == values.size());
        for (int i = 0; i < timestamp.size(); i++) {
            if (timestamp.get(i) == time) {
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
    public List<T> range(double from, double to) {
        assert(from < to);
        assert(timestamp.size() == values.size());
        return Streams.zip(timestamp.stream(), values.stream(), Pair::new)
                .filter(pair -> from <= pair.getFirst() && pair.getFirst() <= to)
                .map(Pair::getSecond)
                .collect(Collectors.toList());
    }
}
