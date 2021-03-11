package org.group_mmm;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * <p>STLAtomic class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class STLOutputAtomic extends STLAbstractAtomic {
    private final List<List<Character>> abstractOutputs = new ArrayList<>();
    private final List<List<Double>> concreteOutputs = new ArrayList<>();
    private List<Character> largest = new ArrayList<>();
    private List<Map<Character, Double>> outputMapper;

    /**
     * <p>Constructor for STLAtomic.</p>
     *
     * @param sigIndex   a int.
     * @param op         a {@link org.group_mmm.STLAbstractAtomic.Operation} object.
     * @param comparator a double.
     */
    public STLOutputAtomic(int sigIndex, Operation op, double comparator) {
        super(sigIndex, op, comparator);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Set<String> getAllAPs() {
        return getAllAPs(abstractOutputs, largest);
    }

    @Override
    protected void constructAtomicStrings() {
        constructAtomicStrings(concreteOutputs, abstractOutputs, largest);
    }

    private void setOutputMaps() {
        abstractOutputs.clear();
        concreteOutputs.clear();
        for (Map<Character, Double> entry : outputMapper) {
            ArrayList<Character> cList = new ArrayList<>(entry.keySet());
            ArrayList<Double> dList = new ArrayList<>(entry.values());
            assert cList.size() == dList.size();
            abstractOutputs.add(cList);
            concreteOutputs.add(dList);
        }
    }

    void setAtomic(List<Map<Character, Double>> outputMapper, List<Character> largest) {
        this.outputMapper = outputMapper;
        this.largest = largest;
        setOutputMaps();
    }

    void setOutputMapper(List<Map<Character, Double>> outputMapper) {
        this.outputMapper = outputMapper;
        setOutputMaps();
    }

    void setLargest(List<Character> largest) {
        this.largest = largest;
        setOutputMaps();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal signal) {
        return getRoSISingle(signal.getOutputSignal());
    }

    @Override
    protected String getSignalName() {
        return "output";
    }
}
