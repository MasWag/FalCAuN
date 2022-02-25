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
    Set<Integer> disprovedIndices = new HashSet<>();

    public StaticSTLList() {
        this(Collections.emptySet());
    }

    public StaticSTLList(STLCost propertyOracle) {
        this(Collections.singleton(propertyOracle));
    }

    public StaticSTLList(Collection<? extends STLCost> STLProperties) {
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
}
