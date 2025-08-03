package net.maswag.falcaun.parser;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import net.maswag.falcaun.IOSignal;

/**
 * This class represents an atomic formula in STL for input signals.
 * 
 * This class has the functions to construct the atomic propositions,
 * a set of alphabets representing the input signal,
 * from the atomic formula and its input mapper.
 * 
 * For example, let an atomic formula be {@literal input(0) > 1.0},
 * the 0-th input mapper be {@literal {a: 1.0, b: 2.0, c: 3.0}}, and
 * the set of alphabets of 1-th input signal be {@literal {'x', 'y'}},
 * then the atomic propositions are {@literal {"bx", "by", "cx", "cy"}}.
 *
 * <p>
 * When the 0-th input mapper is {@literal {a: 1.0, b: 2.0, c: 3.0}},
 * <ul>
 * <li> Given {@literal input(0) < 1.0}, the satisfying 0-th alphabets are {@literal {'a'}}.
 *  Note that {@literal <} ({@literal Operation.lt}) represents a less-than-or-equal-to operator.
 * <li> Given {@literal input(0) == 1.5}, {@code getAllAPs()} raises an {@link RuntimeException}.
 * </ul>
 * 
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class STLInputAtomic extends STLAbstractAtomic {
    private final List<List<Character>> abstractInputs = new ArrayList<>();
    private final List<List<Double>> concreteInputs = new ArrayList<>();
    private List<Map<Character, Double>> inputMapper;

    /**
     * <p>Constructor for STLAtomic.</p>
     * Constructs an atomic proposition {@literal input(sigIndex) op comparator}.
     *
     * @param sigIndex   An index of input signals
     * @param op         The comparison operator {@link Operation}
     * @param comparator The value to compare against
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

    /**
     * Constructs {@code #satisfyingAtomicPropositions} if not initialized.
     */
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
            var errMsg = String.format("%d-th input signal equal to %f does not exist.", index, threshold);
            throw new NoSuchElementException(errMsg);
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

    /**
     * Gives the input mapper for the atomic formula.
     * It is required to construct the atomic propositions.
     * 
     * @param inputMapper The input mapper to set
     */
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
