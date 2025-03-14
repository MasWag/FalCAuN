package net.maswag.falcaun;

import lombok.Getter;
import net.automatalib.word.Word;

import java.util.Objects;

/**
 * Abstract class representing an Input-Output (IO) signal.
 * This class provides a framework for handling input and output signals in a system, ensuring that the input and output signals have the same length.
 *
 * @param <I> Type of the input symbols
 */
@Getter
abstract public class AbstractIOSignal<I> implements IOSignal<I> {
    /**
     * The input signal represented as a Word.
     */
    Word<I> inputSignal;

    /**
     * The output signal represented as a Word.
     */
    Word<I> outputSignal;

    /**
     * Constructs an instance of AbstractIOSignal with the given input and output signals.
     *
     * @param inputSignal  The input signal as a Word.
     * @param outputSignal The output signal as a Word. Must have the same length as the input signal.
     */
    public AbstractIOSignal(Word<I> inputSignal, Word<I> outputSignal) {
        assert (inputSignal.size() == outputSignal.size()) : "Input and output signals must have the same length.";
        assert (inputSignal.isEmpty() || inputSignal.stream().anyMatch(Objects::nonNull)) : "Input signal must not contain null values: " + inputSignal;
        assert (outputSignal.isEmpty() || outputSignal.stream().anyMatch(Objects::nonNull)) : "Output signal must not contain null values" + outputSignal;
        if (outputSignal.stream().anyMatch(Objects::isNull)) {
            throw new RuntimeException("The output signal must not be null");
        }
        this.inputSignal = inputSignal;
        this.outputSignal = outputSignal;
    }

    /**
     * Returns the size of the input signal.
     *
     * @return The number of symbols in the input signal.
     */
    @Override
    public int size() {
        return this.inputSignal.size();
    }

    /**
     * Retrieves the output symbol at the specified index.
     *
     * @param i The index of the output symbol to retrieve.
     * @return The output symbol at the specified index.
     */
    @Override
    public I getOutputSymbol(int i) {
        return outputSignal.getSymbol(i);
    }
}
