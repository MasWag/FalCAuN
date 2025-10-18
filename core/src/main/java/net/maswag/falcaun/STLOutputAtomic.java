package net.maswag.falcaun;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
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
     * @param op         a {@link Operation} object.
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
        return super.getAllAPs(abstractOutputs.size());
    }

    @Override
    public void constructSatisfyingAtomicPropositions() {
        super.constructSatisfyingAtomicPropositions();
        constructAtomicStrings(abstractOutputs.size());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Set<Character> constructSmallerAPs(int index, double threshold) {
        //Each element of concreteValues must be sorted in ascending order.
        var concreteValues = concreteOutputs;
        var abstractValues = abstractOutputs;

        int bsResult = Collections.binarySearch(concreteValues.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? bsResult : (~bsResult - 1);
        Set<Character> resultAPs = new HashSet<>(abstractValues.get(index).subList(0, thresholdIndex + 1));
        return resultAPs;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Set<Character> constructLargerAPs(int index, double threshold) {
        var concreteValues = concreteOutputs;
        var abstractValues = abstractOutputs;

        int bsResult = Collections.binarySearch(concreteValues.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? bsResult : (~bsResult - 1);
        Set<Character> resultAPs = new HashSet<>(abstractValues.get(index).subList(thresholdIndex + 1, abstractValues.get(index).size()));

        resultAPs.add(largest.get(index));

        return resultAPs;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Set<Character> constructEqAPs(int index, double threshold) {
        var concreteValues = concreteOutputs;
        var abstractValues = abstractOutputs;

        int bsResult = Collections.binarySearch(concreteValues.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? bsResult : (~bsResult);
        Set<Character> resultAPs = new HashSet<>();
        if (!abstractValues.get(index).isEmpty()) {
            resultAPs.addAll(abstractValues.get(index).subList(thresholdIndex, thresholdIndex + 1));
        }
        if (abstractValues.get(index).isEmpty() ||
            (bsResult < 0 && thresholdIndex == abstractValues.get(index).size())) {
            resultAPs.add(largest.get(index));
        }
        assert resultAPs.size() == 1;

        return resultAPs;
    }

    /**
     * Construct the characters that represent the abstract values of the signal.
     * largest is also used to construct the atomic propositions.
     * 
     * @param index The index of the signal
     */
    @Override
    protected Set<Character> constructAllAPs(int index) {
        var abstractValues = abstractOutputs;

        Set<Character> resultAPs = new HashSet<>(abstractValues.get(index));
        resultAPs.add(largest.get(index));
        return resultAPs;
    }

    private void setOutputMaps() {
        STLAbstractAtomic.decomposeMapList(outputMapper, abstractOutputs, concreteOutputs);
        initialized = true;
    }

    void setMapper(OutputMapper mapper) {
        this.outputMapper = mapper.getOutputMapper();
        this.largest = mapper.getLargest();
        setOutputMaps();
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

    @Override
    public STLCost toNnf(boolean negate){
        if (negate){
            return new TemporalNot.STLNot(this);
        } else {
            return this;
        }
    }

    @Override
    public STLCost toDisjunctiveForm(){
        return this;
    }

    @Override
    public List<TemporalLogic<List<Double>>> getAllConjunctions(){
        return new ArrayList<>();
    }
}
