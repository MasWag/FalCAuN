package org.group_mmm;

import lombok.Getter;

import java.util.List;

class IOSignalPiece {
    @Getter
    final private List<Double> inputSignal, outputSignal;

    public IOSignalPiece(List<Double> inputSignal, List<Double> outputSignal) {
        this.inputSignal = inputSignal;
        this.outputSignal = outputSignal;
    }
}
