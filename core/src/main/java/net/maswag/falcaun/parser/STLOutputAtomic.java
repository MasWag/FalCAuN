package net.maswag.falcaun.parser;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import net.maswag.falcaun.IOSignal;
import net.maswag.falcaun.OutputMapper;

/**
 * <p>STLAtomic class.</p>
 * This class represents an atomic formula in STL for output signals.
 * 
 * This class has the functions to construct the atomic propositions,
 * a set of alphabets representing the output signal,
 * from the atomic formula and its output mapper.
 * 
 * For example, let an atomic formula be {@literal output(0) > 1.0},
 * the 0-th output mapper be {@literal {a: 1.0, b: 2.0, c: 3.0}},
 * the 0-th largest be {@literal 'd'},
 * the set of alphabets of 1-th output signal be {@literal {'x', 'y'}},
 * and the 1-th largest be {@literal 'z'},
 * then the atomic propositions are {@literal {"bx", "by", "bz", "cx", "cy", "cz", "dx", "dy", "dz"}}.
 *
 * <p>
 * When the 0-th output mapper is {@literal {a: 1.0, b: 2.0, c: 3.0}} and largest is {@literal {'d'}},
 * the comparator in ranges of {@literal (-inf, 1.0], (1.0, 2.0], (2.0, 3.0]} is mapped to {@literal 'a', 'b', 'c'} for each and
 * this in range of (3.0, +inf) is mapped to {@literal 'd'}.
 * 
 * <ul>
 * <li> Given {@literal output(0) > 2.0}, the satisfying 0-th alphabets are {@literal {'c', 'd'}}.
 * <li> Given {@literal output(0) < 1.0}, the satisfying 0-th alphabets are {@literal {'a'}}.
 *  Note that {@literal <} ({@literal Operation.lt}) represents a less-than-or-equal-to operator.
 * <li> Given {@literal output(0) == 4.0}, {@code getAllAPs()} raises an {@link RuntimeException}.
 * </ul>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class STLOutputAtomic extends STLAbstractAtomic {
    private final List<List<Character>> abstractOutputs = new ArrayList<>();
    private final List<List<Double>> concreteOutputs = new ArrayList<>();
    private List<Character> largest;
    private List<Map<Character, Double>> outputMapper;

    /**
     * <p>Constructor for STLOutputAtomic.</p>
     * Constructs an atomic proposition {@literal output(sigIndex) op comparator}.
     *
     * @param sigIndex   An index of output signals
     * @param op         The comparison operator {@link Operation}
     * @param comparator The value to compare against
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

    /**
     * Constructs {@link #satisfyingAtomicPropositions} if not initialized.
     */
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

    public void setAtomic(List<Map<Character, Double>> outputMapper, List<Character> largest) {
        this.outputMapper = outputMapper;
        this.largest = largest;
        setOutputMaps();
    }
    
    /**
     * Gives the output mapper for the atomic formula.
     * It is required to construct the atomic propositions.
     * 
     * @param outputMapper The output mapper to set
     */
    void setOutputMapper(List<Map<Character, Double>> outputMapper) {
        this.outputMapper = outputMapper;
        setOutputMaps();
    }

    /**
     * Gives the largest alphabets for the atomic formula.
     * It is required to construct the atomic propositions.
     * 
     * @param largest The list of largest characters to set
     */
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
