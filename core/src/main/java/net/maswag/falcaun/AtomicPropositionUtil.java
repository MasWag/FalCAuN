package net.maswag.falcaun;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Utility class for constructing abstract atomic propositions.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class AtomicPropositionUtil {

    /**
     * Private constructor to prevent instantiation of utility class.
     */
    private AtomicPropositionUtil() {
        throw new UnsupportedOperationException("Utility class should not be instantiated");
    }

    /**
     * Constructs abstract atomic propositions from abstract outputs and largest outputs.
     * <p>
     * This method generates all possible combinations of abstract output characters by
     * taking the cartesian product of abstract outputs with their corresponding largest outputs.
     * </p>
     *
     * @param abstractOutputs A list of lists of abstract output characters for each component.
     * @param largestOutputs  A list of largest output characters for each component.
     * @return A list of strings representing all possible abstract atomic propositions.
     * @throws IllegalArgumentException if inputs are null, empty, or have mismatched sizes.
     */
    public static List<String> constructAbstractAPs(List<List<Character>> abstractOutputs, List<Character> largestOutputs) {
        // Input validation
        if (abstractOutputs == null) {
            throw new IllegalArgumentException("abstractOutputs cannot be null");
        }
        if (largestOutputs == null) {
            throw new IllegalArgumentException("largestOutputs cannot be null");
        }
        if (abstractOutputs.isEmpty()) {
            throw new IllegalArgumentException("abstractOutputs cannot be empty");
        }
        if (largestOutputs.isEmpty()) {
            throw new IllegalArgumentException("largestOutputs cannot be empty");
        }
        if (abstractOutputs.size() != largestOutputs.size()) {
            throw new IllegalArgumentException(
                String.format("Size mismatch: abstractOutputs.size()=%d, largestOutputs.size()=%d",
                    abstractOutputs.size(), largestOutputs.size()));
        }
        List<String> result = new ArrayList<>();
        for (int i = 0; i < abstractOutputs.size(); i++) {
            List<Character> abstractOutputi = new ArrayList<>(abstractOutputs.get(i));
            abstractOutputi.add(largestOutputs.get(i));
            List<String> tmpList = new ArrayList<>();
            if (result.isEmpty()) {
                tmpList = abstractOutputi.stream().map(String::valueOf).collect(Collectors.toList());
            } else {
                for (String s: result) {
                    for (Character c: abstractOutputi) {
                        tmpList.add(s + c);
                    }
                }
            }
            result = tmpList;
        }
        return result;
    }
}
