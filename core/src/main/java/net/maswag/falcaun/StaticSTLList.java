package net.maswag.falcaun;

import java.util.*;

import net.maswag.falcaun.parser.TemporalLogic;

/**
 * List of STL/LTL formulas without update
 *
 * @author Masaki Waga
 * @param <I> Type of the input at each step.
 * @see BlackBoxVerifier
 * @see NumericSULVerifier
 */
public class StaticSTLList<I> extends AbstractAdaptiveSTLUpdater<I> {
    Set<Integer> disprovedIndices = new HashSet<>();

    public StaticSTLList() {
        this(Collections.emptySet());
    }

    public StaticSTLList(TemporalLogic<I> propertyOracle) {
        this(Collections.singleton(propertyOracle));
    }

    public StaticSTLList(Collection<? extends TemporalLogic<I>> STLProperties) {
        super();
        this.addSTLProperties(STLProperties);
    }

    @Override
    public boolean allDisproved() {
        return getSTLProperties().size() == disprovedIndices.size();
    }

    @Override
    protected void notifyFalsifiedProperty(List<Integer> falsifiedIndices) {
        super.notifyFalsifiedProperty(falsifiedIndices);
        disprovedIndices.addAll(falsifiedIndices);
    }

    @Override
    public void reset() {
        // Since we do not add any STL formula, we do not need to reset.
    }
}
