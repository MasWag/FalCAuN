package net.maswag.falcaun;

import de.learnlib.sul.SULMapper;
import lombok.NonNull;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.word.Word;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

public interface SignalDiscretizer extends SULMapper<String, String, List<Double>, IOSignalPiece<List<Double>>> {
    /**
     * Maps an abstract input string to a concrete list of double values.
     *
     * @param s The abstract input string to map.
     * @return The concrete list of double values corresponding to the input string.
     */
    @Override
    List<Double> mapInput(String s);

    /**
     * Maps a concrete IOSignalPiece to an abstract output string.
     *
     * @param concreteIO The concrete IOSignalPiece to map.
     * @return The abstract output string corresponding to the concrete output.
     */
    @Override
    String mapOutput(IOSignalPiece<List<Double>> concreteIO);

    /**
     * Maps an abstract input word to a concrete word.
     *
     * @param abstractInput The abstract input word to map.
     * @return The concrete word corresponding to the abstract input word.
     */
    default Word<List<Double>> mapInput(@NonNull Word<String> abstractInput) {
        return Word.fromList(abstractInput.stream().map(this::mapInput).collect(Collectors.toList()));
    }

    /**
     * Maps a list of abstract input words to a list of concrete words.
     *
     * @param abstractInputs The list of abstract input words to map.
     * @return The list of concrete words corresponding to the abstract input words.
     */
    default List<Word<List<Double>>> mapInputs(List<Word<String>> abstractInputs) {
        return abstractInputs.stream().map(
                word -> (word == null) ? null : Word.fromList(word.stream().map(this::mapInput).collect(Collectors.toList()))
        ).collect(Collectors.toList());
    }

    /**
     * Maps a concrete IOSignalPiece to a list of concrete output values.
     *
     * @param concreteIO The concrete IOSignalPiece to map.
     * @return The list of concrete output values.
     */
    default List<Double> mapConcrete(IOSignalPiece<List<Double>> concreteIO) {
        if (concreteIO == null || concreteIO.getOutputSignal() == null) {
            throw new IllegalArgumentException(
                    "Concrete IO signal piece or its output signal cannot be null."
            );
        }

        return concreteIO.getOutputSignal();
    }

    /**
     * Provides an optional mapping to transform abstract output strings.
     *
     * @return An {@link Optional} containing the post-output mapper if available, otherwise {@link Optional#empty()}.
     */
    default Optional<Map<String, String>> getPostOutputMapper() {
        return Optional.empty();
    }

    /**
     * Constructs an abstract alphabet from the input mappings.
     *
     * @return The abstract alphabet.
     */
    Alphabet<String> constructAbstractAlphabet();

    /**
     * Constructs a concrete alphabet from the input mappings.
     *
     * @return The concrete alphabet.
     */
    Alphabet<List<Double>> constructConcreteAlphabet();
}
