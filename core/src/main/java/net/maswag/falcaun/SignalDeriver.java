package net.maswag.falcaun;

import de.learnlib.sul.SULMapper;
import lombok.NonNull;
import lombok.extern.slf4j.Slf4j;

import java.util.*;

/**
 * Signal derivation mapper that uses SignalMapper to derive signals from concrete I/O signals.
 * <p>
 * This class implements the SULMapper interface to provide signal derivation functionality.
 * It takes concrete input signals and passes them through unchanged, while for output signals,
 * it uses a SignalMapper to derive additional signals from the concrete I/O signal piece.
 * <p>
 * When composed with SignalAdapter, it provides the same functionality as NumericSULMapper.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class SignalDeriver implements SULMapper<List<Double>, IOSignalPiece<List<Double>>, List<Double>, IOSignalPiece<List<Double>>> {
    private final SignalMapper sigMap;

    /**
     * Constructs a {@link SignalDeriver} from extended signal-mapper definitions.
     * <p>
     * The given definitions are parsed by {@link ExtendedSignalMapper#parse(List)}
     * and the resulting mapper is used to create the returned deriver.
     *
     * @param mapperDefinitions signal-mapper definitions to parse with the extended parser
     * @return a {@link SignalDeriver} configured with the parsed {@link ExtendedSignalMapper}
     */
    public static SignalDeriver parse(List<String> mapperDefinitions) {
        return new SignalDeriver(ExtendedSignalMapper.parse(mapperDefinitions));
    }

    /**
     * Constructs a {@link SignalDeriver} from simple signal-mapper definitions.
     * <p>
     * The given definitions are parsed by {@link SimpleSignalMapper#parse(List)}
     * and the resulting mapper is used to create the returned deriver.
     *
     * @param mapperDefinitions signal-mapper definitions to parse with the simple parser
     * @return a {@link SignalDeriver} configured with the parsed simple {@link SignalMapper}
     */
    public static SignalDeriver parseSimple(List<String> mapperDefinitions) {
        return new SignalDeriver(SimpleSignalMapper.parse(mapperDefinitions));
    }

    /**
     * Constructor for SignalDeriver.
     *
     * @param sigMap The SignalMapper for deriving additional signals.
     */
    public SignalDeriver(@NonNull SignalMapper sigMap) {
        this.sigMap = sigMap;
        log.debug("sigMap size: {}", sigMap.size());
    }

    /**
     * Maps a concrete input signal to itself (pass-through).
     *
     * @param input The concrete input signal.
     * @return The same input signal unchanged.
     */
    @Override
    public List<Double> mapInput(List<Double> input) {
        return input;
    }

    /**
     * Maps a concrete IOSignalPiece to an IOSignalPiece with derived signals.
     * <p>
     * This method takes the original IOSignalPiece, derives additional signals using
     * the SignalMapper, and returns a new IOSignalPiece with the derived signals.
     *
     * @param concreteIO The concrete IOSignalPiece to map.
     * @return A new IOSignalPiece with derived signals.
     */
    @Override
    public IOSignalPiece<List<Double>> mapOutput(IOSignalPiece<List<Double>> concreteIO) {
        List<Double> concreteOutput = concreteIO.getOutputSignal();
        List<Double> derivedOutput = new ArrayList<>(concreteOutput);
        for (int i = 0; i < sigMap.size(); i++) {
            derivedOutput.add(sigMap.apply(i, concreteIO));
        }

        return new IOSignalPiece<>(concreteIO.getInputSignal(), derivedOutput);
    }
}
