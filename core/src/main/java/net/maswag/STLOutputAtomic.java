package net.maswag;

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
    private List<Character> largest;
    private List<Map<Character, Double>> outputMapper;

    /**
     * <p>Constructor for STLAtomic.</p>
     *
     * @param sigIndex   a int.
     * @param op         a {@link net.maswag.STLAbstractAtomic.Operation} object.
     * @param comparator a double.
     */
    public STLOutputAtomic(int sigIndex, Operation op, double comparator) {
        super(sigIndex, op, comparator);
        iOType = IOType.OUTPUT;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Set<String> getAllAPs() {
        return getAllAPs(abstractOutputs, largest);
    }

    @Override
    public void constructSatisfyingAtomicPropositions() {
        if (!this.initialized) {
            if (!this.isInitialized()) {
                throw new IllegalStateException("The formula is not initialized but the abstract string is requested.");
            }
        }
        constructAtomicStrings(concreteOutputs, abstractOutputs, largest);
    }

    private void setOutputMaps() {
        STLAbstractAtomic.decomposeMapList(outputMapper, abstractOutputs, concreteOutputs);
        initialized = true;
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
    public RoSI getRoSI(IOSignal<List<Double>> signal) {
        return getRoSISingle(signal.getOutputSignal());
    }

    @Override
    protected String getSignalName() {
        return "output";
    }
}
