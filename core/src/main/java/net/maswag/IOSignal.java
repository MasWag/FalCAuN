package net.maswag;

import com.google.common.collect.Streams;
import lombok.Getter;
import net.automatalib.word.Word;

import java.util.*;
import java.util.stream.Stream;

@Getter
public class IOSignal<I> {
    Word<I> inputSignal, outputSignal;

    public IOSignal(Word<I> inputSignal, Word<I> outputSignal) {
        assert (inputSignal.size() == outputSignal.size());
        this.inputSignal = inputSignal;
        this.outputSignal = outputSignal;
    }

    public int size() {
        return this.inputSignal.size();
    }

    public int length() {
        return size();
    }

    public Stream<IOSignalPiece<I>> stream() {
        return Streams.zip(inputSignal.stream(), outputSignal.stream(), IOSignalPiece::new);
    }

    public List<IOSignal<I>> prefixes(boolean longestFirst) {
        Queue<Word<I>> inputSiffixes = new LinkedList<>(inputSignal.prefixes(longestFirst));
        Queue<Word<I>> outputSiffixes = new LinkedList<>(outputSignal.prefixes(longestFirst));
        List<IOSignal<I>> result = new ArrayList<>();

        while (!inputSiffixes.isEmpty()) {
            result.add(new IOSignal<>(inputSiffixes.poll(), Objects.requireNonNull(outputSiffixes.poll())));
        }
        return result;
    }

    public List<IOSignal<I>> suffixes(boolean longestFirst) {
        Queue<Word<I>> inputSuffixes = new LinkedList<>(inputSignal.suffixes(longestFirst));
        Queue<Word<I>> outputSuffixes = new LinkedList<>(outputSignal.suffixes(longestFirst));
        List<IOSignal<I>> result = new ArrayList<>();

        while (!inputSuffixes.isEmpty()) {
            result.add(new IOSignal<>(inputSuffixes.poll(), Objects.requireNonNull(outputSuffixes.poll())));
        }
        return result;
    }

    public IOSignal<I> suffix(int suffixLen) {
        return new IOSignal<>(inputSignal.suffix(suffixLen), outputSignal.suffix(suffixLen));
    }

    public IOSignal<I> subWord(int fromIndex) {
        return new IOSignal<>(inputSignal.subWord(fromIndex), outputSignal.subWord(fromIndex));
    }

    public IOSignal<I> subWord(int fromIndex, int toIndex) {
        return new IOSignal<>(inputSignal.subWord(fromIndex, toIndex), outputSignal.subWord(fromIndex, toIndex));
    }

    public boolean isEmpty() {
        return size() == 0;
    }

    public I getOutputSymbol(int i) {
        return outputSignal.getSymbol(i);
    }

    class NumericIOSignal extends IOSignal<List<Double>> {
        public NumericIOSignal(Word<List<Double>> inputSignal, Word<List<Double>> outputSignal) {
            super(inputSignal, outputSignal);
        }
    }

    class LogicalIOSignal extends IOSignal<Set<String>> {
        public LogicalIOSignal(Word<Set<String>> inputSignal, Word<Set<String>> outputSignal) {
            super(inputSignal, outputSignal);
        }
    }
}
