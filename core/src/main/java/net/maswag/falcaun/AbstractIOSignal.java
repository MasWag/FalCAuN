package net.maswag.falcaun;

import lombok.Getter;
import net.automatalib.word.Word;

@Getter
abstract public class AbstractIOSignal<I> implements IOSignal<I> {
    Word<I> inputSignal, outputSignal;

    public AbstractIOSignal(Word<I> inputSignal, Word<I> outputSignal) {
        assert (inputSignal.size() == outputSignal.size());
        this.inputSignal = inputSignal;
        this.outputSignal = outputSignal;
    }

    @Override
    public int size() {
        return this.inputSignal.size();
    }

    @Override
    public I getOutputSymbol(int i) {
        return outputSignal.getSymbol(i);
    }
}
