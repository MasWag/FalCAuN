package net.maswag;

import lombok.AllArgsConstructor;
import lombok.Getter;

import java.util.List;
import java.util.Set;

@Getter @AllArgsConstructor
public class IOSignalPiece<I> {
    final private I inputSignal, outputSignal;

    class NumericIOSignalPiece extends IOSignalPiece<List<Double>> {
        public NumericIOSignalPiece(List<Double> inputSignal, List<Double> outputSignal) {
            super(inputSignal, outputSignal);
        }
    }

    class LogicalIOSignalPiece extends IOSignalPiece<Set<String>> {
        public LogicalIOSignalPiece(Set<String> inputSignal, Set<String> outputSignal) {
            super(inputSignal, outputSignal);
        }
    }
}
