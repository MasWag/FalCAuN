package net.maswag.falcaun;

import java.util.List;
import java.util.stream.Stream;

/**
 * A signal with both input and output values.
 *
 * @param <I> the type of the input and output signals
 */
public interface IOSignal<I> {
    /**
     * Returns the number of steps of the signal.
     *
     * @return the number of steps of the signal.
     */
    int size();

    /**
     * Returns the number of steps of the signal.
     *
     * @return the number of steps of the signal.
     */
    default int length() {
        return size();
    }

    /**
     * Returns a stream of the signal.
     *
     * @return the stream of the signal.
     */
    Stream<IOSignalPiece<I>> stream();

    /**
     * Returns all the prefix of the signal.
     * @param longestFirst if true, the longest prefixes are returned first.
     * @return the list of prefixes of the signal.
     */
    List<IOSignal<I>> prefixes(boolean longestFirst);

    /**
     * Constructs all suffixes of the signal.
     *
     * @param longestFirst if true, the longest suffixes are returned first.
     * @return the list of suffixes of the signal.
     */
    List<IOSignal<I>> suffixes(boolean longestFirst);

    /**
     * Constructs a suffix of the signal.
     *
     * @param suffixLen the length of the suffix
     * @return the suffix of the signal with the given length.
     */
    IOSignal<I> suffix(int suffixLen);

    /**
     * Constructs a sub-signal of the signal.
     *
     * @param fromIndex the start index (inclusive)
     * @return the sub-signal of the signal from the given index (inclusive) to the end of the signal.
     */
    IOSignal<I> subWord(int fromIndex);

    /**
     * Constructs a sub-signal of the signal.
     *
     * @param fromIndex the start index (inclusive)
     * @param toIndex the end index (exclusive)
     * @return the sub-signal of the signal from the given index (inclusive) to the given index (exclusive).
     */
    IOSignal<I> subWord(int fromIndex, int toIndex);

    /**
     * Returns true if the signal is empty.
     *
     * @return true if the signal is empty.
     */
    default boolean isEmpty() {
        return size() == 0;
    }

    /**
     * Returns the input symbol at the given index.
     *
     * @param i the index
     */
    I getOutputSymbol(int i);


    /**
     * Returns the input signal.
     *
     * @return the input signal as a word.
     */
    net.automatalib.word.Word<I> getInputSignal();

    /**
     * Returns the output signal.
     * @return the output signal as a word.
     */
    net.automatalib.word.Word<I> getOutputSignal();
}
