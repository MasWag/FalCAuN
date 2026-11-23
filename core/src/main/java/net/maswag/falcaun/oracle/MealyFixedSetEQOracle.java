package net.maswag.falcaun.oracle;

import de.learnlib.oracle.EquivalenceOracle;
import de.learnlib.oracle.MembershipOracle;
import de.learnlib.oracle.equivalence.AbstractTestWordEQOracle;
import lombok.Getter;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.word.Word;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Stream;

/**
 * Equivalence oracle that tests a fixed list of input words in the order of their addition.
 * <p>
 * Each word is answered by the membership oracle when a hypothesis is tested, i.e., the outputs are not fixed when the
 * words are added. The membership queries, the comparison with the hypothesis, and the termination at the first
 * counterexample are by {@link AbstractTestWordEQOracle}.
 * <p>
 * This oracle does not check whether the properties are already disproved. {@link net.maswag.falcaun.verification.BlackBoxVerifier#addEqOracle}
 * wraps it with {@link StopDisprovedEQOracle} for that.
 */
public class MealyFixedSetEQOracle extends AbstractTestWordEQOracle<MealyMachine<?, String, ?, String>, String, Word<String>>
        implements EquivalenceOracle.MealyEquivalenceOracle<String, String>, EvaluationCountable.MealyEquivalenceOracle<String, String> {
    private final List<Word<String>> fixedSamples = new ArrayList<>();
    /**
     * The number of the words evaluated by this oracle, including the ones answered by a cache of the membership
     * oracle. A word is counted each time it is evaluated.
     */
    @Getter
    private int evaluateCount = 0;

    /**
     * @param memOracle the membership oracle used to test the equivalence.
     */
    public MealyFixedSetEQOracle(MembershipOracle.MealyMembershipOracle<String, String> memOracle) {
        // We do not batch the queries so that the words after the first counterexample are not evaluated.
        super(memOracle);
    }

    public void add(Word<String> sample) {
        fixedSamples.add(sample);
    }

    public void addAll(Collection<Word<String>> samples) {
        fixedSamples.addAll(samples);
    }

    /**
     * {@inheritDoc}
     * <p>
     * Without batching, {@link AbstractTestWordEQOracle} consumes the stream one word at a time and stops at the first
     * counterexample. Thus, counting the words when they are consumed counts exactly the evaluated words.
     */
    @Override
    public Stream<Word<String>> generateTestWords(MealyMachine<?, String, ?, String> hypothesis, Collection<? extends String> inputs) {
        return fixedSamples.stream().peek(sample -> evaluateCount++);
    }
}
