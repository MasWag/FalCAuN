package net.maswag.falcaun;

import de.learnlib.sul.SULMapper;
import net.automatalib.alphabet.Alphabet;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * SignalDiscretizer post-composed with an SULMapper.
 *
 * <p>This class allows for the composition of a {@link SignalDiscretizer} with another
 * {@link SULMapper}. The {@code discretizer} handles the mapping between concrete signals
 * and abstract input/output strings. The {@code postMapper} is applied only to the abstract
 * output strings produced by the discretizer; it does not affect how concrete inputs are
 * mapped to abstract inputs.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class PostComposedSignalDiscretizer implements SignalDiscretizer {
    private ComponentWiseSignalDiscretizer discretizer;
    private SULMapper<String, String, String, String> postMapper;

    /**
     * Protected default constructor for PostComposedSignalDiscretizer.
     * <p>
     * This constructor initializes the discretizer and postMapper to {@code null}.
     * It is intended for use by subclasses (such as {@link NumericSULMapperWithSGA})
     * that need to perform custom initialization before setting these fields.
     * Subclasses must call {@link #setDiscretizer(ComponentWiseSignalDiscretizer)} and
     * {@link #setPostMapper(SULMapper)} to initialize the fields before using any methods
     * that depend on them. External users should use
     * {@link #PostComposedSignalDiscretizer(ComponentWiseSignalDiscretizer, SULMapper)}
     * instead.
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
        ensureDiscretizerInitialized();
        // Delegate to discretizer
        return discretizer.mapInput(s);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String mapOutput(IOSignalPiece<List<Double>> concreteIO) {
        ensureInitialized();
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
        ensureDiscretizerInitialized();
        // Delegate to discretizer
        return discretizer.constructAbstractAlphabet();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Alphabet<List<Double>> constructConcreteAlphabet() {
        ensureDiscretizerInitialized();
        // Delegate to discretizer
        return discretizer.constructConcreteAlphabet();
    }

    /**
     * Ensures that the discretizer is initialized.
     *
     * @throws IllegalStateException if discretizer is null
     */
    private void ensureDiscretizerInitialized() {
        if (discretizer == null) {
            throw new IllegalStateException("Discretizer has not been initialized. Call setDiscretizer() before using this method.");
        }
    }

    /**
     * Ensures that both discretizer and postMapper are initialized.
     *
     * @throws IllegalStateException if discretizer or postMapper is null
     */
    private void ensureInitialized() {
        ensureDiscretizerInitialized();
        if (postMapper == null) {
            throw new IllegalStateException("PostMapper has not been initialized. Call setPostMapper() before using this method.");
        }
    }

    /**
     * Sets the discretizer for this PostComposedSignalDiscretizer.
     * <p>
     * This method is protected and intended for use by subclasses that use the
     * protected default constructor. Subclasses must call this method to initialize
     * the discretizer before using any methods that depend on it.
     * </p>
     *
     * @param discretizer The ComponentWiseSignalDiscretizer to use for mapping.
     */
    protected void setDiscretizer(ComponentWiseSignalDiscretizer discretizer) {
        this.discretizer = discretizer;
    }

    /**
     * Sets the postMapper for this PostComposedSignalDiscretizer.
     * <p>
     * This method is protected and intended for use by subclasses that use the
     * protected default constructor. Subclasses must call this method to initialize
     * the postMapper before using any methods that depend on it.
     * </p>
     *
     * @param postMapper The SULMapper to post-compose with the discretizer.
     */
    protected void setPostMapper(SULMapper<String, String, String, String> postMapper) {
        this.postMapper = postMapper;
    }

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
