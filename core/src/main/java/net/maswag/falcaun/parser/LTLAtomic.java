package net.maswag.falcaun.parser;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import net.maswag.falcaun.IOSignal;
import net.maswag.falcaun.LTLAPs;
import net.maswag.falcaun.LTLFormulaBase;
import net.maswag.falcaun.parser.TemporalLogic.IOType;
import net.maswag.falcaun.parser.TemporalLogic.LTLFormula;

/**
 * The atomic propositions in LTL formulas
 */
public class LTLAtomic extends AbstractTemporalLogic<String> implements TemporalLogic.LTLFormula {
    private final LTLFormulaBase formulaBase = new LTLFormulaBase();
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

    /**
     * {@inheritDoc}
     */
    @Override
    public void setAPs(LTLAPs aps) {
        formulaBase.setAps(aps);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public LTLAPs getAPs() {
        return formulaBase.getAps();
    }

    /**
     * Returns all atomic propositions from the appropriate set based on the IO type.
     * Requires that APs have been set via setAPs() before calling this method.
     *
     * @return Set of atomic propositions based on the IO type (input, output, or both)
     * @throws IllegalStateException if APs have not been set
     */
    @Override
    public Set<String> getAllAPs() {
        LTLAPs aps = formulaBase.getAps();
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
    public String toOwlString(){
        if (inputString.isPresent()) { return inputString.get(); }
        else if (outputString.isPresent()) { return outputString.get(); }
        else { return "true"; }
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

    @Override
    public LTLFormula toNnf(boolean negate){
        if (negate){
            return new TemporalNot.LTLNot(this);
        } else {
            return this;
        }
    }

    @Override
    public LTLFormula toDisjunctiveForm(){
        return this;
    }

    @Override
    public List<TemporalLogic<String>> getAllConjunctions(){
        return new ArrayList<>();
    }
}
