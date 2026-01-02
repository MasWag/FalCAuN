package net.maswag.falcaun;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Regression tests for {@link NumericSULMapperWithSGA}.
 */
class NumericSULMapperWithSGATest {

    @Test
    void mapConcreteShouldReturnDerivedOutputs() {
        // Arrange: one-dimensional input/output with a derived signal appended by SignalMapper
        List<Map<Character, Double>> inputMapper = List.of(Map.of('a', 1.0));
        List<Map<Character, Double>> outputMapper = List.of(Map.of('a', 0.0), Map.of('a', 1.0));
        List<Character> largestOutputs = List.of('b', 'b');
        SignalMapper signalMapper = SimpleSignalMapper.parse(List.of("signal(0) + 1.0"));

        NumericSULMapperWithSGA mapper = new NumericSULMapperWithSGA(
                inputMapper,
                largestOutputs,
                outputMapper,
                signalMapper,
                Collections.emptyList(),
                false);

        // Act: mapInput should work as usual
        assertEquals(List.of(1.0), mapper.mapInput("a"));

        IOSignalPiece<List<Double>> ioPiece = new IOSignalPiece<>(List.of(1.0), List.of(2.0));

        // Act: The original output is "bb" but mapped to "aa" after postOutputMapping
        assertTrue(mapper.getPostOutputMapper().isPresent());
        assertEquals("aa", mapper.getPostOutputMapper().get().get("bb"));
        assertEquals("aa", mapper.mapOutput(ioPiece));

        // Act: mapConcrete should include the derived signal from SignalMapper
        List<Double> mapped = mapper.mapConcrete(ioPiece);

        // Assert: the derived component (2.0 + 1.0) is present
        assertEquals(List.of(2.0, 3.0), mapped);
    }
}