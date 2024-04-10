package net.maswag;

import lombok.AllArgsConstructor;
import net.maswag.TemporalLogic.LTLFormula;

import java.util.*;

/**
 * The atomic propositions in LTL formulas
 */
@AllArgsConstructor
public class LTLAtomic extends AbstractTemporalLogic<String> implements LTLFormula {
    private final Optional<String> inputString, outputString;

    @Override
    public Set<String> getAllAPs() {
        Set<String> result = new HashSet<>();
        result.add(inputString.orElse(outputString.orElse("")));
        result.add(outputString.orElse(inputString.orElse("")));
        return result;
    }

    @Override
    public void constructAtomicStrings() {}

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
