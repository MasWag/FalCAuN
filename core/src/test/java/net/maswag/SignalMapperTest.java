package net.maswag;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;

import static java.lang.Math.abs;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class SignalMapperTest {
    private final String PWD = System.getenv("PWD");
    private final String sigMapName = PWD + "/src/test/resources/sigMap.txt";
    SignalMapper sigMap;
    List<Double> concreteSignal;

    @BeforeEach
    void setUp() {
        Function<IOSignalPiece<List<Double>>, Double> diff = a -> a.getOutputSignal().get(0) - a.getOutputSignal().get(1);
        sigMap = new SignalMapper(Collections.singletonList(diff));
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
        sigMap = SignalMapper.parse(sigMapName);
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
}