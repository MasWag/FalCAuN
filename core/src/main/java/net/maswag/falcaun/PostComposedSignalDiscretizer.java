package net.maswag.falcaun;

import de.learnlib.sul.SULMapper;
import net.automatalib.alphabet.Alphabet;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * SignalDiscretizer post-composed with an SULMapper
 *
 * <p>This class allows for the composition of a SignalDiscretizer with another SULMapper.
 * We assume that the SULMapper does not change the input values, i.e., it acts as an identity function.
 * </p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class PostComposedSignalDiscretizer implements SignalDiscretizer {
    private ComponentWiseSignalDiscretizer discretizer;
    private SULMapper<String, String, String, String> postMapper;

    /**
     * Default constructor for PostComposedSignalDiscretizer.
     * <p>
     * This constructor initializes the discretizer and postMapper to null.
     * When using this constructor, ensure to set the discretizer and postMapper before use.
     * </p>
     */
    protected PostComposedSignalDiscretizer() {
        this.discretizer = null;
        this.postMapper = null;
    }

    /**
     * Constructor for PostComposedSignalDiscretizer.
     *
     * @param discretizer The SignalDiscretizer to use for mapping.
     * @param postMapper  The SULMapper to post-compose with the discretizer.
     */
    public PostComposedSignalDiscretizer(
            ComponentWiseSignalDiscretizer discretizer,
            SULMapper<String, String, String, String> postMapper) {
        this.discretizer = discretizer;
        this.postMapper = postMapper;
    }

    @Override
    public List<Double> mapInput(String s) {
        // Delegate to discretizer
        return discretizer.mapInput(s);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String mapOutput(IOSignalPiece<List<Double>> concreteIO) {
        // First, map to abstract output using discretizer
        String abstractOutput = discretizer.mapOutput(concreteIO);
        // Then, apply postMapper to the abstract output
        return postMapper.mapOutput(abstractOutput);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Alphabet<String> constructAbstractAlphabet() {
        // Delegate to discretizer
        return discretizer.constructAbstractAlphabet();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Alphabet<List<Double>> constructConcreteAlphabet() {
        // Delegate to discretizer
        return discretizer.constructConcreteAlphabet();
    }

    protected void setDiscretizer(ComponentWiseSignalDiscretizer discretizer) {
        this.discretizer = discretizer;
    }

    protected void setPostMapper(SULMapper<String, String, String, String> postMapper) {
        this.postMapper = postMapper;
    }

    public static List<String> constructAbstractAPs(List<List<Character>> abstractOutputs, List<Character> largestOutputs) {
        List<String> result = new ArrayList<>();
        for (int i = 0; i < abstractOutputs.size(); i++){
            List<Character> abstractOutputi = new ArrayList<>(abstractOutputs.get(i));
            abstractOutputi.add(largestOutputs.get(i));
            List<String> tmpList = new ArrayList<>();
            if (result.isEmpty()){
                tmpList = abstractOutputi.stream().map(String::valueOf).collect(Collectors.toList());
            } else {
                for (String s: result) {
                    for (Character c : abstractOutputi) {
                        tmpList.add(s + c);
                    }
                }
            }
            result = tmpList;
        }
        return result;
    }
}
