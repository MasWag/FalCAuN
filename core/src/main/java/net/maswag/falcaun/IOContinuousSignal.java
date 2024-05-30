package net.maswag.falcaun;

import com.google.common.collect.Streams;
import lombok.Getter;
import net.automatalib.word.Word;
import org.apache.commons.math3.util.Pair;

import java.util.*;
import java.util.stream.Stream;

/**
 * A signal with continuous output values.
 *
 * @param <I> the type of the input and output signals
 */
@Getter
public class IOContinuousSignal<I> extends AbstractIOSignal<I> {
    ValueWithTime<I> continuousOutputSignal;
    Double signalStep;

    public IOContinuousSignal(Word<I> inputSignal, Word<I> outputSignal, ValueWithTime<I> continuousOutputSignal, Double signalStep) {
        super(inputSignal, outputSignal);
        this.continuousOutputSignal = continuousOutputSignal;
        this.signalStep = signalStep;
    }

    @Override
    public Stream<IOSignalPiece<I>> stream() {
        return Streams.zip(Streams.zip(inputSignal.stream(), outputSignal.stream(), Pair::new),
                continuousOutputSignal.stream(this.signalStep),
                (pair, value) -> new ExtendedIOSignalPiece<>(pair.getFirst(), pair.getSecond(), value));
    }

    @Override
    public List<IOSignal<I>> prefixes(boolean longestFirst) {
        Queue<Word<I>> inputPrefixes = new LinkedList<>(inputSignal.prefixes(longestFirst));
        Queue<Word<I>> outputPrefixes = new LinkedList<>(outputSignal.prefixes(longestFirst));
        List<IOSignal<I>> result = new ArrayList<>();

        while (!inputPrefixes.isEmpty()) {
            Word<I> inputPrefix = inputPrefixes.poll();
            if (inputPrefix.isEmpty()) {
                result.add(new IOContinuousSignal<>(inputPrefix,
                        Objects.requireNonNull(outputPrefixes.poll()),
                        new ValueWithTime<>(), // We use the empty values
                        signalStep));
            } else {
                // The first signal is at 0
                double endTime = signalStep * (inputPrefix.size() - 1);
                result.add(new IOContinuousSignal<>(inputPrefix,
                        Objects.requireNonNull(outputPrefixes.poll()),
                        continuousOutputSignal.range(Double.NEGATIVE_INFINITY, endTime),
                        signalStep));
            }
        }
        return result;
    }

    @Override
    public List<IOSignal<I>> suffixes(boolean longestFirst) {
        double endTime = Double.POSITIVE_INFINITY;
        Queue<Word<I>> inputSuffixes = new LinkedList<>(inputSignal.suffixes(longestFirst));
        Queue<Word<I>> outputSuffixes = new LinkedList<>(outputSignal.suffixes(longestFirst));
        List<IOSignal<I>> result = new ArrayList<>();

        while (!inputSuffixes.isEmpty()) {
            Word<I> inputSuffix = inputSuffixes.poll();
            if (inputSuffix.isEmpty()) {
                result.add(new IOContinuousSignal<>(inputSuffix,
                        Objects.requireNonNull(outputSuffixes.poll()),
                        new ValueWithTime<>(), // We use the empty values
                        signalStep));
            } else {
                // The first signal is at 0
                double beginTime = signalStep * (inputSignal.size() - inputSuffix.size());
                result.add(new IOContinuousSignal<>(inputSuffix,
                        Objects.requireNonNull(outputSuffixes.poll()),
                        continuousOutputSignal.range(beginTime, endTime),
                        signalStep));
            }
        }
        return result;
    }

    @Override
    public IOSignal<I> suffix(int suffixLen) {
        double beginTime = signalStep * (inputSignal.size() - suffixLen);
        return new IOContinuousSignal<>(inputSignal.suffix(suffixLen), outputSignal.suffix(suffixLen),
                continuousOutputSignal.range(beginTime, Double.POSITIVE_INFINITY), signalStep);
    }

    @Override
    public IOSignal<I> subWord(int fromIndex) {
        double beginTime = signalStep * fromIndex;
        return new IOContinuousSignal<>(inputSignal.subWord(fromIndex), outputSignal.subWord(fromIndex),
                continuousOutputSignal.range(beginTime, Double.POSITIVE_INFINITY), signalStep);
    }

    /** {@inheritDoc} */
    @Override
    public IOSignal<I> subWord(int fromIndex, int toIndex) {
        double beginTime = signalStep * fromIndex;
        double endTime = signalStep * toIndex;
        return new IOContinuousSignal<>(inputSignal.subWord(fromIndex, toIndex),
                outputSignal.subWord(fromIndex, toIndex),
                continuousOutputSignal.range(beginTime, endTime), signalStep);
    }
}
