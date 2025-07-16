package net.maswag.falcaun.parser;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import net.maswag.falcaun.IOSignalPiece;
import net.maswag.falcaun.parser.SimpleSignalMapper;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;

import static java.lang.Math.abs;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class SimpleSignalMapperTest {
    private final String PWD = System.getenv("PWD");
    private final String sigMapName = PWD + "/src/test/resources/sigMap.txt";
    SignalMapper sigMap;
    List<Double> concreteSignal;

    @BeforeEach
    void setUp() {
        Function<IOSignalPiece<List<Double>>, Double> diff = a -> a.getOutputSignal().get(0) - a.getOutputSignal().get(1);
        sigMap = new SimpleSignalMapper(Collections.singletonList(diff));
        concreteSignal = new ArrayList<>();
        concreteSignal.add(2.0);
        concreteSignal.add(-4.2);
        concreteSignal.add(0.4);
    }

    @Test
    void apply() {
        assertEquals(6.2, sigMap.apply(0, new IOSignalPiece<>(Collections.emptyList(), concreteSignal)));
        // sigMap should be applied to an index smaller than the size of the SigMap. Otherwise, it throws IndexOutOfBoundsException.
        assertThrows(IndexOutOfBoundsException.class, () -> sigMap.apply(2,
                new IOSignalPiece<>(Collections.emptyList(), concreteSignal)));
    }

    @Test
    void size() {
        assertEquals(1, sigMap.size());
    }

    @Test
    void parse() throws IOException {
        sigMap = SimpleSignalMapper.parse(sigMapName);
        assertEquals(4, sigMap.size());
        assertEquals(2.0 + 0.4, sigMap.apply(0,
                new IOSignalPiece<>(Collections.emptyList(), concreteSignal)));
        assertEquals(-4.2 - 0.4 * 2.0, sigMap.apply(1,
                new IOSignalPiece<>(Collections.emptyList(), concreteSignal)));
        assertEquals(0.5 + 2.0, sigMap.apply(2,
                new IOSignalPiece<>(Collections.singletonList(0.5), concreteSignal)));
        assertEquals(abs(2.0 - 4.2), sigMap.apply(3,
                new IOSignalPiece<>(Collections.emptyList(), concreteSignal)));
        assertThrows(IndexOutOfBoundsException.class, () -> sigMap.apply(4,
                new IOSignalPiece<>(Collections.emptyList(), concreteSignal)));
    }

    @Test
    void mod() {
        String expr = "output(1) % 4";
        sigMap = SimpleSignalMapper.parse(Collections.singletonList(expr));
        // The size of mapper should be 1.
        assertEquals(1, sigMap.size());
        // The result of the expression should be 7.0 % 4 = 3.0.
        concreteSignal.set(1, 7.0);
        assertEquals(3.0, sigMap.apply(0, new IOSignalPiece<>(Collections.emptyList(), concreteSignal)));
        // The result of the expression should be -4.2 % 4 = -0.2 (with some numerical error).
        concreteSignal.set(1, -4.2);
        assertEquals(-0.2, sigMap.apply(0, new IOSignalPiece<>(Collections.emptyList(), concreteSignal)), 1e-10);
    }

    @Test
    void min() {
        String expr = "min(output(0), 3)";
        sigMap = SimpleSignalMapper.parse(Collections.singletonList(expr));
        // The size of mapper should be 1.
        assertEquals(1, sigMap.size());
        // The result of the expression should be min(2.0, 3) = 2.0.
        assertEquals(2.0, sigMap.apply(0, new IOSignalPiece<>(Collections.emptyList(), concreteSignal)));
        // The result of the expression should be min(4.2, 3) = 3.0.
        concreteSignal.set(0, 4.2);
        assertEquals(3.0, sigMap.apply(0, new IOSignalPiece<>(Collections.emptyList(), concreteSignal)));
    }

    @Test
    void max() {
        String expr = "max(output(0), 3)";
        sigMap = SimpleSignalMapper.parse(Collections.singletonList(expr));
        // The size of mapper should be 1.
        assertEquals(1, sigMap.size());
        // The result of the expression should be max(2.0, 3) = 3.0.
        assertEquals(3.0, sigMap.apply(0, new IOSignalPiece<>(Collections.emptyList(), concreteSignal)));
        // The result of the expression should be max(4.2, 3) = 4.2.
        concreteSignal.set(0, 4.2);
        assertEquals(4.2, sigMap.apply(0, new IOSignalPiece<>(Collections.emptyList(), concreteSignal)));
    }
}
