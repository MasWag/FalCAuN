package net.maswag;

import net.maswag.TemporalLogic.LTLFormula;

import java.util.*;

/**
 * The atomic propositions in LTL formulas
 */
public class LTLAtomic extends AbstractTemporalLogic<String> implements LTLFormula {
    private final Optional<String> inputString, outputString;

    public LTLAtomic(Optional<String> inputString, Optional<String> outputString) {
        this.inputString = inputString;
        this.outputString = outputString;
        this.nonTemporal = false;
        this.initialized = true;
        if (inputString.isPresent() && outputString.isPresent()) {
            this.iOType = IOType.BOTH;
        } else if (inputString.isPresent()) {
            this.iOType = IOType.INPUT;
        } else if (outputString.isPresent()) {
            this.iOType = IOType.OUTPUT;
        } else {
            throw new IllegalArgumentException("At least one of inputString and outputString must be present");
        }
    }

    @Override
    public Set<String> getAllAPs() {
        Set<String> result = new HashSet<>();
        result.add(inputString.orElse(outputString.orElse("")));
        result.add(outputString.orElse(inputString.orElse("")));
        return result;
    }

    @Override
    public void constructSatisfyingAtomicPropositions() {}

    @Override
    public String toAbstractString() {
        List<String> result = new ArrayList<>();
        inputString.ifPresent(s -> result.add("input == \"" + s + "\" "));
        outputString.ifPresent(s -> result.add("output == \"" + s + "\" "));
        return String.join(" && ", result);
    }

    @Override
    public String toString() {
        return this.toAbstractString();
    }

    @Override
    public RoSI getRoSI(IOSignal<String> signal) {
        if (signal.isEmpty()) {
            return new RoSI(Double.NEGATIVE_INFINITY, Double.POSITIVE_INFINITY);
        } else if (inputString.isPresent() && ! inputString.get().equals(signal.getInputSignal().getSymbol(0)) ||
                outputString.isPresent() && ! outputString.get().equals(signal.getOutputSignal().getSymbol(0))) {
            return new RoSI(Double.NEGATIVE_INFINITY, Double.NEGATIVE_INFINITY);
        } else {
            return new RoSI(Double.POSITIVE_INFINITY, Double.POSITIVE_INFINITY);
        }
    }
}
