package net.maswag.falcaun;

import com.google.common.collect.Streams;
import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.word.Word;
import org.apache.commons.math3.util.Pair;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * A signal with continuous output values.
 *
 * @param <I> the type of the input and output signals
 */
@Slf4j
@Getter
public class IOContinuousSignal<I> extends AbstractIOSignal<I> {
    ValueWithTime<I> continuousOutputSignal;
    Double signalStep;

    /**
     * Constructor for the continuous signal.
     * <p>
     * The input and output signals must have the same length. The continuous output signal values must be left-right inclusive.
     * </p>
     *
     * @param inputSignal            the input signal
     * @param outputSignal           the output signal
     * @param continuousOutputSignal the continuous output signal values with time stamps
     * @param signalStep             the time between each element of inputSignal and outputSignal
     */
    public IOContinuousSignal(Word<I> inputSignal, Word<I> outputSignal, ValueWithTime<I> continuousOutputSignal, double signalStep) {
        super(inputSignal, outputSignal);
        if (inputSignal.size() != outputSignal.size()) {
            throw new IllegalArgumentException("The input and output signals must have the same length");
        }
        if (inputSignal.isEmpty() != continuousOutputSignal.isEmpty()) {
            throw new IllegalArgumentException("The input signal and the continuous output signal must be both empty or non-empty");
        }
        if (!inputSignal.isEmpty() && inputSignal.size() - 1 != Math.floor(continuousOutputSignal.duration() / signalStep)) {
            log.error("Inconsistent duration is detected: inputSignal.size() = " + inputSignal.size() + ", signalStep = " + signalStep + ", continuousOutputSignal.duration() = " + continuousOutputSignal.duration());
            throw new IllegalArgumentException("The duration of the continuous output signal must be consistent with the input signal");
        }
        this.continuousOutputSignal = continuousOutputSignal;
        this.signalStep = signalStep;
    }

    @Override
    public Stream<IOSignalPiece<I>> stream() {
        if (inputSignal.size() > continuousOutputSignal.stream(this.signalStep).toList().size()) {
            throw new IllegalArgumentException("The signal step must be consistent with the input signal");
        }
        if (this.continuousOutputSignal.stream(this.signalStep).anyMatch(Objects::isNull)) {
            throw new RuntimeException("The continuous output signal must not be null");
        }
        return Streams.zip(Streams.zip(inputSignal.stream(), outputSignal.stream(), Pair::new),
                continuousOutputSignal.stream(this.signalStep).limit(inputSignal.size()),
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
                int i = Collections.binarySearch(continuousOutputSignal.timestamps, endTime);
                int index = i >= 0 ? i : i <= -continuousOutputSignal.size() - 1 ? continuousOutputSignal.size() - 1 : -i - 1;
                endTime = continuousOutputSignal.timestamps.get(index);
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
                        continuousOutputSignal.range(beginTime, endTime, true, true),
                        signalStep));
            }
        }
        return result;
    }

    @Override
    public IOSignal<I> suffix(int suffixLen) {
        double beginTime = signalStep * (inputSignal.size() - suffixLen);
        return new IOContinuousSignal<>(inputSignal.suffix(suffixLen), outputSignal.suffix(suffixLen),
                continuousOutputSignal.range(beginTime, Double.POSITIVE_INFINITY, true, true), signalStep);
    }

    @Override
    public IOSignal<I> subWord(int fromIndex) {
        double beginTime = signalStep * fromIndex;
        return new IOContinuousSignal<>(inputSignal.subWord(fromIndex), outputSignal.subWord(fromIndex),
                continuousOutputSignal.range(beginTime, Double.POSITIVE_INFINITY, true, true), signalStep);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public IOSignal<I> subWord(int fromIndex, int toIndex) {
        double beginTime = signalStep * fromIndex;
        double endTime = signalStep * (toIndex - 1);
        return new IOContinuousSignal<>(inputSignal.subWord(fromIndex, toIndex),
                outputSignal.subWord(fromIndex, toIndex),
                continuousOutputSignal.range(beginTime, endTime, true, true), signalStep);
    }
}
