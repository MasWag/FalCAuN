package net.maswag;

import com.google.common.collect.Streams;
import lombok.Getter;
import net.automatalib.word.Word;

import java.util.*;
import java.util.stream.Stream;

/**
 * A discrete-time signal with both input and output values.
 *
 * @param <I> the type of the input and output signals
 */
public class IODiscreteSignal<I> extends AbstractIOSignal<I> {
    public IODiscreteSignal(Word<I> inputSignal, Word<I> outputSignal) {
        super(inputSignal, outputSignal);
    }

    @Override
    public Stream<IOSignalPiece<I>> stream() {
        return Streams.zip(inputSignal.stream(), outputSignal.stream(), IOSignalPiece::new);
    }

    @Override
    public List<IOSignal<I>> prefixes(boolean longestFirst) {
        Queue<Word<I>> inputPrefixes = new LinkedList<>(inputSignal.prefixes(longestFirst));
        Queue<Word<I>> outputPrefixes = new LinkedList<>(outputSignal.prefixes(longestFirst));
        List<IOSignal<I>> result = new ArrayList<>();

        while (!inputPrefixes.isEmpty()) {
            result.add(new IODiscreteSignal<>(inputPrefixes.poll(), Objects.requireNonNull(outputPrefixes.poll())));
        }
        return result;
    }

    @Override
    public List<IOSignal<I>> suffixes(boolean longestFirst) {
        Queue<Word<I>> inputSuffixes = new LinkedList<>(inputSignal.suffixes(longestFirst));
        Queue<Word<I>> outputSuffixes = new LinkedList<>(outputSignal.suffixes(longestFirst));
        List<IOSignal<I>> result = new ArrayList<>();

        while (!inputSuffixes.isEmpty()) {
            result.add(new IODiscreteSignal<>(inputSuffixes.poll(), Objects.requireNonNull(outputSuffixes.poll())));
        }
        return result;
    }

    @Override
    public IOSignal<I> suffix(int suffixLen) {
        return new IODiscreteSignal<>(inputSignal.suffix(suffixLen), outputSignal.suffix(suffixLen));
    }

    @Override
    public IOSignal<I> subWord(int fromIndex) {
        return new IODiscreteSignal<>(inputSignal.subWord(fromIndex), outputSignal.subWord(fromIndex));
    }

    /** {@inheritDoc} */
    @Override
    public IOSignal<I> subWord(int fromIndex, int toIndex) {
        return new IODiscreteSignal<>(inputSignal.subWord(fromIndex, toIndex), outputSignal.subWord(fromIndex, toIndex));
    }
}
