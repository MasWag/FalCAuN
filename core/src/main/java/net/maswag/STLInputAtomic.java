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
public class STLInputAtomic extends STLAbstractAtomic {
    private final List<List<Character>> abstractInputs = new ArrayList<>();
    private final List<List<Double>> concreteInputs = new ArrayList<>();
    private final List<Character> largest = new ArrayList<>();
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
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Set<String> getAllAPs() {
        return getAllAPs(abstractInputs, largest);
    }

    @Override
    public void constructAtomicStrings() {
        constructAtomicStrings(concreteInputs, abstractInputs, largest);
    }

    private void setInputMaps() {
        abstractInputs.clear();
        concreteInputs.clear();
        for (Map<Character, Double> entry : inputMapper) {
            ArrayList<Character> cList = new ArrayList<>(entry.keySet());
            ArrayList<Double> dList = new ArrayList<>(entry.values());
            assert cList.size() == dList.size();
            abstractInputs.add(cList);
            concreteInputs.add(dList);
        }
        largest.clear();
        for (List<Character> inputList : abstractInputs) {
            largest.add((char) (inputList.get(inputList.size() - 1) + 1));
        }
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
