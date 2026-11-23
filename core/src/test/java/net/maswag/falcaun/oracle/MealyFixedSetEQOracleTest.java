package net.maswag.falcaun.oracle;

import de.learnlib.driver.simulator.MealySimulatorSUL;
import de.learnlib.filter.cache.mealy.MealyCaches;
import de.learnlib.oracle.MembershipOracle;
import de.learnlib.oracle.membership.SULOracle;
import de.learnlib.query.DefaultQuery;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.alphabet.impl.ArrayAlphabet;
import net.automatalib.automaton.transducer.impl.CompactMealy;
import net.automatalib.util.automaton.builder.AutomatonBuilders;
import net.automatalib.word.Word;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class MealyFixedSetEQOracleTest {
    private final Alphabet<String> alphabet = new ArrayAlphabet<>("a", "b");
    /**
     * The target outputs "x" for "a" and "y" for "b".
     */
    private CompactMealy<String, String> target;
    /**
     * The hypothesis differs from the target only after "b b".
     */
    private CompactMealy<String, String> hypothesis;
    /**
     * The words answered by the target, in the order of the queries.
     */
    private final List<Word<String>> executed = new ArrayList<>();
    private MembershipOracle.MealyMembershipOracle<String, String> recordingOracle;

    @BeforeEach
    void setUp() {
        target = AutomatonBuilders.forMealy(new CompactMealy<String, String>(alphabet))
                .withInitial("q0")
                .from("q0").on("a").withOutput("x").loop()
                .from("q0").on("b").withOutput("y").loop()
                .create();
        hypothesis = AutomatonBuilders.forMealy(new CompactMealy<String, String>(alphabet))
                .withInitial("q0")
                .from("q0").on("a").withOutput("x").loop()
                .from("q0").on("b").withOutput("y").to("q1")
                .from("q1").on("a").withOutput("x").to("q0")
                .from("q1").on("b").withOutput("x").to("q0")
                .create();
        SULOracle<String, String> sulOracle = new SULOracle<>(new MealySimulatorSUL<>(target));
        executed.clear();
        recordingOracle = queries -> {
            for (var query : queries) {
                executed.add(query.getInput());
            }
            sulOracle.processQueries(queries);
        };
    }

    @Test
    void evaluatesInOrderAndStopsAtFirstCounterexample() {
        MealyFixedSetEQOracle oracle = new MealyFixedSetEQOracle(recordingOracle);
        oracle.add(Word.fromSymbols("a", "a"));
        oracle.addAll(List.of(Word.fromSymbols("a", "b"), Word.fromSymbols("b", "b"), Word.fromSymbols("b", "b", "a")));

        DefaultQuery<String, Word<String>> cex = oracle.findCounterExample(hypothesis, alphabet);
        assertNotNull(cex);
        assertEquals(Word.fromSymbols("b", "b"), cex.getInput());
        assertEquals(Word.fromSymbols("y", "y"), cex.getOutput());
        // The words are evaluated in the order of their addition, and the word after the counterexample is not evaluated
        assertEquals(List.of(Word.fromSymbols("a", "a"), Word.fromSymbols("a", "b"), Word.fromSymbols("b", "b")), executed);
        assertEquals(3, oracle.getEvaluateCount());
    }

    @Test
    void noCounterexample() {
        MealyFixedSetEQOracle oracle = new MealyFixedSetEQOracle(recordingOracle);
        oracle.addAll(List.of(Word.fromSymbols("a"), Word.fromSymbols("b", "a")));
        assertNull(oracle.findCounterExample(hypothesis, alphabet));
        assertEquals(2, oracle.getEvaluateCount());
    }

    /**
     * The evaluation count includes the words answered by a cache of the membership oracle.
     */
    @Test
    void evaluationCountIncludesCacheHits() {
        MealyFixedSetEQOracle oracle = new MealyFixedSetEQOracle(MealyCaches.createTreeCache(alphabet, recordingOracle));
        oracle.addAll(List.of(Word.fromSymbols("a"), Word.fromSymbols("b", "a")));
        assertNull(oracle.findCounterExample(hypothesis, alphabet));
        assertNull(oracle.findCounterExample(hypothesis, alphabet));
        assertEquals(4, oracle.getEvaluateCount());
        // The second evaluations are answered by the cache
        assertEquals(2, executed.size());
    }

    @Test
    void emptyInputs() {
        MealyFixedSetEQOracle oracle = new MealyFixedSetEQOracle(recordingOracle);
        oracle.add(Word.fromSymbols("b", "b"));
        assertNull(oracle.findCounterExample(hypothesis, Collections.emptyList()));
        assertEquals(0, oracle.getEvaluateCount());
        assertTrue(executed.isEmpty());
    }
}
