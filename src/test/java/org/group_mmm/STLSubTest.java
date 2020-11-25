package org.group_mmm;

import net.automatalib.words.Word;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

class STLSubTest {
    private Word<List<Double>> signal;

    @BeforeEach
    void setUp() {
        signal = Word.epsilon();
    }

    @Test
    void applyShortEventual() {
        STLCost fml = new STLSub(new STLEventually(new STLAtomic(0, STLAtomic.Operation.gt, 10.0)), 1, 3);
        double expect = Double.POSITIVE_INFINITY;
        double actual = fml.apply(signal);
        assertEquals(expect, actual);
    }

    @Test
    void applyShortGlobal() {
        STLCost fml = new STLSub(new STLGlobal(new STLAtomic(0, STLAtomic.Operation.gt, 10.0)), 1, 3);
        double expect = Double.POSITIVE_INFINITY;
        double actual = fml.apply(signal);
        assertEquals(expect, actual);
    }

    @Test
    void toAbstractStringShortEventual() {
        STLAtomic atomic = new STLAtomic(0, STLAtomic.Operation.gt, 10.0);

        Map<Character, Double> outputMap = new HashMap<>();
        outputMap.put('a', 10.0);
        List<Map<Character, Double>> outputMapper = Collections.singletonList(outputMap);
        List<Character> largest = Collections.singletonList('b');
        atomic.setAtomic(outputMapper, largest);

        STLCost fml = new STLSub(new STLEventually(atomic), 1, 3);
        // Optimization
        // String expect = "( X (( output == \"b\" ) ) ) || ( X (X (( output == \"b\" ) ) ) ) || ( X (X (X (( output == \"b\" ) ) ) ) )";
        String expect = "( (X (( ( output == \"b\" ) ) || (X (( ( output == \"b\" ) ) || (X (( ( output == \"b\" ) ) ) ) ) ) ) ) )";
        String actual = fml.toAbstractString();
        assertEquals(expect, actual);
    }

    @Test
    void toAbstractStringShortGlobal() {
        STLAtomic atomic = new STLAtomic(0, STLAtomic.Operation.lt, 10.0);

        Map<Character, Double> outputMap = new HashMap<>();
        outputMap.put('a', 10.0);
        List<Map<Character, Double>> outputMapper = Collections.singletonList(outputMap);
        List<Character> largest = Collections.singletonList('b');
        atomic.setAtomic(outputMapper, largest);

        STLCost fml = new STLSub(new STLGlobal(atomic), 1, 3);
        // Optimization
        // String expect = "( X (( output == \"a\" ) ) ) && ( X (X (( output == \"a\" ) ) ) ) && ( X (X (X (( output == \"a\" ) ) ) ) )";
        String expect = "( (X (( ( output == \"a\" ) ) && (X (( ( output == \"a\" ) ) && (X (( ( output == \"a\" ) ) ) ) ) ) ) ) )";
        String actual = fml.toAbstractString();
        assertEquals(expect, actual);
    }

    @Test
    void toAbstractStringS3() {
        Map<Character, Double> outputMap = new HashMap<>();
        outputMap.put('a', 53.0);
        outputMap.put('b', 57.0);
        List<Map<Character, Double>> outputMapper = Collections.singletonList(outputMap);
        List<Character> largest = Collections.singletonList('c');

        STLAtomic atomic_left = new STLAtomic(0, STLAtomic.Operation.lt, 53.0);
        atomic_left.setAtomic(outputMapper, largest);
        STLAtomic atomic_right = new STLAtomic(0, STLAtomic.Operation.gt, 57.0);
        atomic_right.setAtomic(outputMapper, largest);

        STLCost fml = new STLSub(new STLGlobal(new STLOr(atomic_left, atomic_right)), 1, 3);
        String expect = "( (X (( ( output == \"a\" ) || ( output == \"c\" ) ) && (X (( ( output == \"a\" ) || ( output == \"c\" ) ) && (X (( ( output == \"a\" ) || ( output == \"c\" ) ) ) ) ) ) ) ) )";
        String actual = fml.toAbstractString();
        assertEquals(expect, actual);

    }
}