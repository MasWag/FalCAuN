package net.maswag.falcaun;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.*;

class ValueWithTimeTest {
    ValueWithTime<List<Double>> valueWithTime;

    @BeforeEach
    void setUp() {
        List<Double> timestamps = List.of(0.0, 1.0, 2.0, 3.0, 4.0);
        List<List<Double>> values = List.of(
                List.of(1.0, 2.0, 3.0, 4.0, 5.0),
                List.of(2.0, 3.0, 4.0, 5.0, 6.0),
                List.of(3.0, 4.0, 5.0, 6.0, 7.0),
                List.of(4.0, 5.0, 6.0, 7.0, 8.0),
                List.of(5.0, 6.0, 7.0, 8.0, 9.0)
        );
        valueWithTime = new ValueWithTime<>(timestamps, values);
    }

    @Test
    void at() {
        assertEquals(1.0, Objects.requireNonNull(valueWithTime.at(0.0)).get(0));
        assertEquals(2.0, Objects.requireNonNull(valueWithTime.at(1.0)).get(0));
        assertEquals(3.0, Objects.requireNonNull(valueWithTime.at(2.0)).get(0));
        assertEquals(4.0, Objects.requireNonNull(valueWithTime.at(3.0)).get(0));
        assertEquals(5.0, Objects.requireNonNull(valueWithTime.at(4.0)).get(0));
    }

    @Test
    void range() {
        // Extract the values for 1.0 < t <= 3.0
        ValueWithTime<List<Double>> ranged = valueWithTime.range(1.0, 3.0);
        assertEquals(2, ranged.size());
        assertEquals(3.0, ranged.getValues().get(0).get(0));
        assertEquals(4.0, ranged.getValues().get(1).get(0));
    }

    @Test
    void stream() {
        // Make a list with sampling interval 2.0
        List<List<List<Double>>> sampledValues = valueWithTime.stream(2.0).collect(Collectors.toList());
        // In total, the number of samples should be 3
        assertEquals(3, sampledValues.size());
        // The first sample should have the value at 0.0
        assertEquals(1, sampledValues.get(0).size());
        assertEquals(1.0, sampledValues.get(0).get(0).get(0));
        // The second sample should have the value at 1.0 and 2.0
        assertEquals(2, sampledValues.get(1).size());
        assertEquals(2.0, sampledValues.get(1).get(0).get(0));
        assertEquals(3.0, sampledValues.get(1).get(1).get(0));
        // The third sample should have the value at 3.0 and 4.0
        assertEquals(2, sampledValues.get(2).size());
        assertEquals(4.0, sampledValues.get(2).get(0).get(0));
        assertEquals(5.0, sampledValues.get(2).get(1).get(0));
    }
}