package net.maswag.falcaun.parser;

import java.util.*;

import net.maswag.falcaun.IOSignal;
import net.maswag.falcaun.parser.TemporalLogic.IOType;
import net.maswag.falcaun.parser.TemporalLogic.LTLFormula;

/**
 * The atomic propositions in LTL formulas
 */
public class LTLAtomic extends AbstractTemporalLogic<String> implements TemporalLogic.LTLFormula {
    private final Optional<String> inputString, outputString;

    public LTLAtomic(Optional<String> inputString, Optional<String> outputString) {
        this.inputString = inputString;
        this.outputString = outputString;
        this.nonTemporal = true;
        this.initialized = true;
        if (inputString.isPresent() && outputString.isPresent()) {
            this.iOType = IOType.BOTH;
        } else if (inputString.isPresent()) {
            this.iOType = IOType.INPUT;
            this.satisfyingAtomicPropositions = Collections.singleton(inputString.get());
        } else if (outputString.isPresent()) {
            this.iOType = IOType.OUTPUT;
            this.satisfyingAtomicPropositions = Collections.singleton(outputString.get());
        } else {
            throw new IllegalArgumentException("At least one of inputString and outputString must be present");
        }
    }

    /*
     * Typically, we need to return the set of atomic propositions, but it is not possible to get all atomic propositions.
     * Instead, we return the set of atomic propositions that are satisfied by the formula, which works for the current implementation.
     */
    @Override
    public Set<String> getAllAPs() {
        Set<String> result = new HashSet<>();
        result.add(inputString.orElse(outputString.orElse("")));
        result.add(outputString.orElse(inputString.orElse("")));
        return result;
    }

    // We construct satisfyingAtomicPropositions in the constructor. So, we don't need to do anything here.
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
