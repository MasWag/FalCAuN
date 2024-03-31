package net.maswag;

import com.google.common.collect.Streams;
import lombok.Getter;
import net.automatalib.word.Word;

import java.util.*;
import java.util.stream.Stream;

@Getter
public class IOSignal {
    Word<List<Double>> inputSignal, outputSignal;

    public IOSignal(Word<List<Double>> inputSignal, Word<List<Double>> outputSignal) {
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

    public Stream<IOSignalPiece> stream() {
        return Streams.zip(inputSignal.stream(), outputSignal.stream(), IOSignalPiece::new);
    }

    public List<IOSignal> prefixes(boolean longestFirst) {
        Queue<Word<List<Double>>> inputSiffixes = new LinkedList<>(inputSignal.prefixes(longestFirst));
        Queue<Word<List<Double>>> outputSiffixes = new LinkedList<>(outputSignal.prefixes(longestFirst));
        List<IOSignal> result = new ArrayList<>();

        while (!inputSiffixes.isEmpty()) {
            result.add(new IOSignal(inputSiffixes.poll(), Objects.requireNonNull(outputSiffixes.poll())));
        }
        return result;
    }

    public List<IOSignal> suffixes(boolean longestFirst) {
        Queue<Word<List<Double>>> inputSiffixes = new LinkedList<>(inputSignal.suffixes(longestFirst));
        Queue<Word<List<Double>>> outputSiffixes = new LinkedList<>(outputSignal.suffixes(longestFirst));
        List<IOSignal> result = new ArrayList<>();

        while (!inputSiffixes.isEmpty()) {
            result.add(new IOSignal(inputSiffixes.poll(), Objects.requireNonNull(outputSiffixes.poll())));
        }
        return result;
    }

    public IOSignal suffix(int suffixLen) {
        return new IOSignal(inputSignal.suffix(suffixLen), outputSignal.suffix(suffixLen));
    }

    public IOSignal subWord(int fromIndex) {
        return new IOSignal(inputSignal.subWord(fromIndex), outputSignal.subWord(fromIndex));
    }

    public IOSignal subWord(int fromIndex, int toIndex) {
        return new IOSignal(inputSignal.subWord(fromIndex, toIndex), outputSignal.subWord(fromIndex, toIndex));
    }

    public boolean isEmpty() {
        return size() == 0;
    }

    public List<Double> getOutputSymbol(int i) {
        return outputSignal.getSymbol(i);
    }
}
