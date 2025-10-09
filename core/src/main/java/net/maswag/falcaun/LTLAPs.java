package net.maswag.falcaun;

import lombok.Getter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Represents the atomic propositions (APs) for LTL formulas.
 * This class holds the complete set of possible input and output values
 * that can appear in an LTL formula, which is necessary for correctly
 * computing the negation of atomic propositions.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class LTLAPs {
    @Getter
    private final Set<String> inputAPs;
    @Getter
    private final Set<String> outputAPs;

    /**
     * Creates an empty set of atomic propositions.
     */
    public LTLAPs() {
        this.inputAPs = new HashSet<>();
        this.outputAPs = new HashSet<>();
    }

    /**
     * Creates atomic propositions with the specified input and output APs.
     *
     * @param inputAPs  The list of input atomic propositions
     * @param outputAPs The list of output atomic propositions
     */
    public LTLAPs(List<String> inputAPs, List<String> outputAPs) {
        this.inputAPs = new HashSet<>(inputAPs);
        this.outputAPs = new HashSet<>(outputAPs);
    }

    /**
     * Adds an input atomic proposition.
     *
     * @param ap The atomic proposition to add
     */
    public void addInputAP(String ap) {
        inputAPs.add(ap);
    }

    /**
     * Adds an output atomic proposition.
     *
     * @param ap The atomic proposition to add
     */
    public void addOutputAP(String ap) {
        outputAPs.add(ap);
    }

    /**
     * Merges another set of atomic propositions into this one.
     *
     * @param other The atomic propositions to merge
     */
    public void merge(LTLAPs other) {
        this.inputAPs.addAll(other.inputAPs);
        this.outputAPs.addAll(other.outputAPs);
    }

    /**
     * Creates a copy of these atomic propositions.
     *
     * @return A new LTLAPs with the same atomic propositions
     */
    public LTLAPs copy() {
        return new LTLAPs(new ArrayList<>(inputAPs), new ArrayList<>(outputAPs));
    }
}