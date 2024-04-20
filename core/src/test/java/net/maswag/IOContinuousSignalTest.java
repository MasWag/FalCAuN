package net.maswag;

import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.stream.Collectors;

import static java.lang.Math.ceil;
import static org.junit.jupiter.api.Assertions.*;

class IOContinuousSignalTest {
    IOContinuousSignal<List<Double>> signal;

    @BeforeEach
    void setUp() {
        double signalStep = 2.0;
        Word<List<Double>> inputSignal = Word.fromList(List.of(
                List.of(10.0, 12.0),
                List.of(12.0, 14.0),
                List.of(14.0, 16.0)));
        ValueWithTime<List<Double>> valueWithTime;
        List<Double> timestamps = List.of(0.0, 1.0, 2.0, 3.0, 4.0);
        List<List<Double>> values = List.of(
                List.of(1.0, 2.0, 3.0, 4.0, 5.0),
                List.of(2.0, 3.0, 4.0, 5.0, 6.0),
                List.of(3.0, 4.0, 5.0, 6.0, 7.0),
                List.of(4.0, 5.0, 6.0, 7.0, 8.0),
                List.of(5.0, 6.0, 7.0, 8.0, 9.0)
        );
        valueWithTime = new ValueWithTime<>(timestamps, values);
        WordBuilder<List<Double>> outputSignalBuilder = new WordBuilder<>();
        for (int i = 0; i < 3; i++) {
            outputSignalBuilder.append(valueWithTime.at(i * signalStep));
        }
        signal = new IOContinuousSignal<>(inputSignal, outputSignalBuilder.toWord(), valueWithTime, signalStep);
    }

    @Test
    void size() {
        // Since the signal step is 2.0, we have the values at 0.0, 2.0, and 4.0.
        assertEquals(3, signal.size());
    }

    @Test
    void stream() {
        // Make a list from the stream. Each element is a piece of the signal at 0.0, 2.0, and 4.0.
        List<IOSignalPiece<List<Double>>> pieces = signal.stream().collect(Collectors.toList());
        assertEquals(3, pieces.size());
        // It must be an object of ExtendedIOSignalPiece, which is a child of IOSignalPiece.
        assertInstanceOf(ExtendedIOSignalPiece.class, pieces.get(0));
        // The first piece is at 0.0
        assertEquals(1.0, pieces.get(0).getOutputSignal().get(0));
        assertEquals(1, ((ExtendedIOSignalPiece<List<Double>>) pieces.get(0)).getPreviousOutputSignals().size());
        // The second piece is at 2.0, which has the previous output signal at 1.0 and the current output signal at 2.0
        assertEquals(3.0, pieces.get(1).getOutputSignal().get(0));
        assertEquals(2, ((ExtendedIOSignalPiece<List<Double>>) pieces.get(1)).getPreviousOutputSignals().size());
        // The third piece is at 4.0, which has the previous output signals at 3.0 and the current output signal at 4.0
        assertEquals(5.0, pieces.get(2).getOutputSignal().get(0));
        assertEquals(2, ((ExtendedIOSignalPiece<List<Double>>) pieces.get(2)).getPreviousOutputSignals().size());
    }

    @Test
    void prefixes() {
        // We have the prefixes to 4.0, 2.0, and 0.0
        List<IOSignal<List<Double>>> prefixes = signal.prefixes(true);
        assertEquals(4, prefixes.size());
        // The first prefix is of length 3
        assertEquals(3, prefixes.get(0).getOutputSignal().size());
        assertEquals(5.0, prefixes.get(0).getOutputSignal().asList().get(2).get(0));
        // The second prefix is of length 2
        assertEquals(2, prefixes.get(1).getOutputSignal().size());
        assertEquals(3.0, prefixes.get(1).getOutputSignal().asList().get(1).get(0));
        // The third prefix is of length 1
        assertEquals(1, prefixes.get(2).getOutputSignal().size());
        assertEquals(1.0, prefixes.get(2).getOutputSignal().asList().get(0).get(0));
        // The forth prefix is of length 0 (the empty word)
        assertEquals(0, prefixes.get(3).getOutputSignal().size());
    }

    @Test
    void suffixes() {
        // We have the suffixes from 0.0, 2.0, and 4.0
        List<IOSignal<List<Double>>> suffixes = signal.suffixes(true);
        assertEquals(4, suffixes.size());
        // The first suffix is of length 3
        assertEquals(3, suffixes.get(0).getOutputSignal().size());
        assertEquals(1.0, suffixes.get(0).getOutputSignal().asList().get(0).get(0));
        // The second suffix is of length 2
        assertEquals(2, suffixes.get(1).getOutputSignal().size());
        assertEquals(3.0, suffixes.get(1).getOutputSignal().asList().get(0).get(0));
        // The third suffix is of length 1
        assertEquals(1, suffixes.get(2).getOutputSignal().size());
        assertEquals(5.0, suffixes.get(2).getOutputSignal().asList().get(0).get(0));
        // The forth suffix is of length 0 (the empty word)
        assertEquals(0, suffixes.get(3).getOutputSignal().size());
    }

    @Test
    void suffix() {
        // The suffix of length 2 should have the values at 2.0 and 4.0
        IOSignal<List<Double>> suffix = signal.suffix(2);
        assertEquals(2, suffix.getOutputSignal().size());
        assertEquals(3.0, suffix.getOutputSignal().asList().get(0).get(0));
        assertEquals(5.0, suffix.getOutputSignal().asList().get(1).get(0));
    }

    @Test
    void subWord() {
        // The subword from index 2 should have the value at 4.0
        IOSignal<List<Double>> subWord = signal.subWord(2);
        assertEquals(1, subWord.getOutputSignal().size());
        assertEquals(5.0, subWord.getOutputSignal().asList().get(0).get(0));
    }

    @Test
    void subWordTwo() {
        // It returns a sub-signal of the signal from the given index (inclusive) to the given index (exclusive).
        // The subword from index 1 to 2 should have the value at 2.0
        IOSignal<List<Double>> subWord = signal.subWord(1, 2);
        assertEquals(1, subWord.getOutputSignal().size());
        assertEquals(3.0, subWord.getOutputSignal().asList().get(0).get(0));
    }
}