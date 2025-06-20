package net.maswag.falcaun;

import java.util.*;

/**
 * <p>STLAtomic class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class STLInputAtomic extends STLAbstractAtomic {
    private final List<List<Character>> abstractInputs = new ArrayList<>();
    private final List<List<Double>> concreteInputs = new ArrayList<>();
    private List<Map<Character, Double>> inputMapper;

    /**
     * <p>Constructor for STLAtomic.</p>
     *
     * @param sigIndex   a int.
     * @param op         a {@link Operation} object.
     * @param comparator a double.
     */
    public STLInputAtomic(int sigIndex, Operation op, double comparator) {
        super(sigIndex, op, comparator);
        iOType = IOType.INPUT;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Set<String> getAllAPs() {
        return super.getAllAPs(abstractInputs.size());
    }

    @Override
    public void constructSatisfyingAtomicPropositions() {
        super.constructSatisfyingAtomicPropositions();
        constructAtomicStrings(abstractInputs.size());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Set<Character> constructSmallerAPs(int index, double threshold) {
        //Each element of concreteValues must be sorted in ascending order.
        var concreteValues = concreteInputs;
        var abstractValues = abstractInputs;

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
        var concreteValues = concreteInputs;
        var abstractValues = abstractInputs;

        int bsResult = Collections.binarySearch(concreteValues.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? (bsResult + 1) : (~bsResult);
        Set<Character> resultAPs = new HashSet<>(abstractValues.get(index).subList(thresholdIndex, abstractValues.get(index).size()));

        return resultAPs;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Set<Character> constructEqAPs(int index, double threshold) {
        var concreteValues = concreteInputs;
        var abstractValues = abstractInputs;

        int bsResult = Collections.binarySearch(concreteValues.get(index), threshold);
        if (bsResult < 0) {
            var errMsg = String.format("%d-th input signal equals to %f does not exist.", index, threshold);
            throw new RuntimeException(errMsg);
        }
        return Set.of(abstractValues.get(index).get(bsResult));
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected Set<Character> constructAllAPs(int index) {
        var abstractValues = abstractInputs;
        return new HashSet<>(abstractValues.get(index));
    }

    private void setInputMaps() {
        STLAbstractAtomic.decomposeMapList(inputMapper, abstractInputs, concreteInputs);
        initialized = true;
    }

    void setInputMapper(List<Map<Character, Double>> inputMapper) {
        this.inputMapper = inputMapper;
        setInputMaps();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public RoSI getRoSI(IOSignal<List<Double>> signal) {
        return getRoSISingle(signal.getInputSignal());
    }

    @Override
    protected String getSignalName() {
        return "input";
    }
}
