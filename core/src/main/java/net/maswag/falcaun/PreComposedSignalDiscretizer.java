package net.maswag.falcaun;

import de.learnlib.sul.SULMapper;
import net.automatalib.alphabet.Alphabet;

import java.util.List;

/**
 * SignalDiscretizer pre-composed with an SULMapper
 *
 * <p>This class allows for the composition of a SignalDiscretizer with another SULMapper.
 * We assume that the SULMapper does not change the input values (i.e., it acts as an identity function on inputs),
 * a property that is enforced in {@link #mapInput(String)}. The {@code preMapper} may, however, derive additional
 * signals in the outputs, which are then discretized by the underlying {@link ComponentWiseSignalDiscretizer}.
 * </p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class PreComposedSignalDiscretizer implements ComponentWiseSignalDiscretizer {
    private final ComponentWiseSignalDiscretizer discretizer;
    private final SULMapper<List<Double>, IOSignalPiece<List<Double>>, List<Double>, IOSignalPiece<List<Double>>> preMapper;

    /**
     * Constructor for PreComposedSignalDiscretizer.
     *
     * @param discretizer The SignalDiscretizer to use for mapping.
     * @param preMapper   The SULMapper to pre-compose with the discretizer.
     */
    public PreComposedSignalDiscretizer(
            ComponentWiseSignalDiscretizer discretizer,
            SULMapper<List<Double>, IOSignalPiece<List<Double>>, List<Double>, IOSignalPiece<List<Double>>> preMapper) {
        this.discretizer = discretizer;
        this.preMapper = preMapper;
    }

    @Override
    public List<Double> mapInput(String s) {
        // Delegate to discretizer
        List<Double> concreteInput = discretizer.mapInput(s);
        // Ensure that preMapper does not change input values
        List<Double> mappedInput = preMapper.mapInput(concreteInput);
        if (concreteInput == null ? mappedInput != null : !concreteInput.equals(mappedInput)) {
            throw new IllegalStateException("PreMapper changed input values, which is not allowed.");
        }
        return concreteInput;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String mapOutput(IOSignalPiece<List<Double>> concreteIO) {
        // First, derive additional signals using preMapper
        IOSignalPiece<List<Double>> mappedOutput = preMapper.mapOutput(concreteIO);

        // Then map to abstract output using discretizer
        return discretizer.mapOutput(mappedOutput);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public List<Double> mapConcrete(IOSignalPiece<List<Double>> concreteIO) {
        // First, derive additional signals using preMapper
        IOSignalPiece<List<Double>> derivedIO = preMapper.mapOutput(concreteIO);

        // Then map to abstract output using discretizer
        return discretizer.mapConcrete(derivedIO);
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

    /**
     * {@inheritDoc}
     */
    @Override
    public List<Character> getLargestOutputs() {
        // Delegate to discretizer
        return this.discretizer.getLargestOutputs();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public List<List<Character>> getAbstractOutputs() {
        // Delegate to discretizer
        return this.discretizer.getAbstractOutputs();
    }

}
