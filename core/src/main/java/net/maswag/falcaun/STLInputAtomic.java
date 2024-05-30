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
    private final List<Character> largest = Collections.emptyList();
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
        return getAllAPs(abstractInputs, largest);
    }

    @Override
    public void constructSatisfyingAtomicPropositions() {
        if (!this.initialized) {
            if (!this.isInitialized()) {
                throw new IllegalStateException("The formula is not initialized but the abstract string is requested.");
            }
        }
        constructAtomicStrings(concreteInputs, abstractInputs, largest);
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
