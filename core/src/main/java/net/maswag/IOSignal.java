package net.maswag;

import java.util.List;
import java.util.stream.Stream;

/**
 * A signal with both input and output values.
 */
public interface IOSignal<I> {
    /**
     * Returns the number of steps of the signal.
     */
    int size();

    /**
     * Returns the number of steps of the signal.
     */
    default int length() {
        return size();
    }

    Stream<IOSignalPiece<I>> stream();

    List<IOSignal<I>> prefixes(boolean longestFirst);

    List<IOSignal<I>> suffixes(boolean longestFirst);

    IOSignal<I> suffix(int suffixLen);

    IOSignal<I> subWord(int fromIndex);

    /**
     * Return a sub-signal of the signal from the given index (inclusive) to the given index (exclusive).
     */
    IOSignal<I> subWord(int fromIndex, int toIndex);

    /**
     * Returns true if the signal is empty.
     */
    default boolean isEmpty() {
        return size() == 0;
    }

    I getOutputSymbol(int i);

    net.automatalib.word.Word<I> getInputSignal();

    net.automatalib.word.Word<I> getOutputSignal();
}
