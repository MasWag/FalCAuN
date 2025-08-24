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