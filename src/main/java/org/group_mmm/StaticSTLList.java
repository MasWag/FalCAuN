package org.group_mmm;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

/**
 * List of STL/LTL formulas without update
 *
 * @author Masaki Waga
 * @see BlackBoxVerifier
 * @see SimulinkVerifier
 */
public class StaticSTLList extends AbstractAdaptiveSTLUpdater {
    private final List<STLCost> STLproperties;

    public StaticSTLList() {
        this(Collections.emptySet());
    }

    public StaticSTLList(STLCost propertyOracle) {
        this(Collections.singleton(propertyOracle));
    }

    public StaticSTLList(Collection<? extends STLCost> STLproperties) {
        this.STLproperties = new ArrayList<>(STLproperties);
    }

    @Override
    public List<STLCost> getSTLProperties() {
        return STLproperties;
    }

    @Override
    protected void notifyFalsifiedProperty(int i) {
        this.STLproperties.remove(i);
    }
}
