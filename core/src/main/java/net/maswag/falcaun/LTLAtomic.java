package net.maswag.falcaun;

import java.util.*;

/**
 * The atomic propositions in LTL formulas
 */
public class LTLAtomic extends AbstractLTLFormula {
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
     * Returns all atomic propositions. If APs are set, returns the appropriate
     * set from the APs. Otherwise, returns just the APs from this atomic formula.
     */
    @Override
    public Set<String> getAllAPs() {
        if (aps == null) {
            throw new IllegalStateException("Atomic propositions (APs) have not been set. " +
                    "Ensure that APs are initialized before calling getAllAPs().");
        }
        
        // Return the appropriate set from the APs
        if (iOType == IOType.INPUT) {
            return aps.getInputAPs();
        } else if (iOType == IOType.OUTPUT) {
            return aps.getOutputAPs();
        } else {
            // For BOTH type, we might need to return both sets
            // This is a fallback for edge cases
            Set<String> result = new HashSet<>();
            inputString.ifPresent(result::add);
            outputString.ifPresent(result::add);
            return result;
        }
    }

    @Override
    public void collectAtomicPropositions(LTLAPs aps) {
        inputString.ifPresent(aps::addInputAP);
        outputString.ifPresent(aps::addOutputAP);
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
