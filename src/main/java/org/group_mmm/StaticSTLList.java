package org.group_mmm;

import java.util.*;

/**
 * List of STL/LTL formulas without update
 *
 * @author Masaki Waga
 * @see BlackBoxVerifier
 * @see SimulinkVerifier
 */
public class StaticSTLList extends AbstractAdaptiveSTLUpdater {
    private final List<STLCost> STLProperties;
    Set<Integer> disprovedIndices = new HashSet<>();

    public StaticSTLList() {
        this(Collections.emptySet());
    }

    public StaticSTLList(STLCost propertyOracle) {
        this(Collections.singleton(propertyOracle));
    }

    public StaticSTLList(Collection<? extends STLCost> STLProperties) {
        this.STLProperties = new ArrayList<>(STLProperties);
    }

    @Override
    public boolean allDisproved() {
        return STLProperties.size() == disprovedIndices.size();
    }

    @Override
    public List<STLCost> getSTLProperties() {
        return STLProperties;
    }

    @Override
    protected void notifyFalsifiedProperty(List<Integer> falsifiedIndices) {
        super.notifyFalsifiedProperty(falsifiedIndices);
        disprovedIndices.addAll(falsifiedIndices);
    }
}
