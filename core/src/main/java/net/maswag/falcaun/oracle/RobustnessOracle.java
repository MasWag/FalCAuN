package net.maswag.falcaun.oracle;

import de.learnlib.query.Query;
import lombok.AccessLevel;
import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.alphabet.Alphabet;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;
import net.maswag.falcaun.signal.IOSignal;

import java.util.List;
import java.util.function.Function;

/**
 * Answers membership queries together with the robustness value for a cost function.
 * <p>
 * The SUL is executed by the {@link NumericMembershipOracle} that created this oracle. This oracle owns only the
 * robustness cache for its cost function, which maps an abstract input word to the robustness values of its prefixes.
 * The cache is filled by the executions requested by this oracle or by the oracles registered before it.
 *
 * @see NumericMembershipOracle#registerCostFunction(Function)
 */
@Slf4j
public class RobustnessOracle implements EvaluationCountable {
    private final NumericMembershipOracle owner;
    @Getter(AccessLevel.PACKAGE)
    private final Function<IOSignal<List<Double>>, Double> costFunc;
    private final IncrementalMealyTreeBuilder<String, Double> robustnessCache;
    /**
     * The number of the SUL executions triggered by this oracle.
     */
    @Getter
    private int evaluateCount = 0;

    RobustnessOracle(NumericMembershipOracle owner, Function<IOSignal<List<Double>>, Double> costFunc, Alphabet<String> abstractAlphabet) {
        this.owner = owner;
        this.costFunc = costFunc;
        this.robustnessCache = new IncrementalMealyTreeBuilder<>(abstractAlphabet);
    }

    /**
     * Answers the query and returns the robustness value of its input word.
     * <p>
     * The SUL is executed if the abstract output or the robustness value is not cached, or if the cached robustness
     * value is infinite.
     *
     * @param query the query to answer
     * @return the robustness value of the input word of the query
     */
    double processQueryWithCost(Query<String, Word<String>> query) {
        final Word<String> input = query.getInput();
        WordBuilder<String> output = new WordBuilder<>(input.size());
        WordBuilder<Double> robustness = new WordBuilder<>(input.size());

        if (!owner.lookup(input, output) || !robustnessCache.lookup(input, robustness)
                || robustness.toWord().lastSymbol().isInfinite()) {
            evaluateCount++;
            output.clear();
            output.append(owner.execute(input, this));
            robustness.clear();
            robustnessCache.lookup(input, robustness);
            if (robustness.toWord().lastSymbol().isInfinite()) {
                log.warn("Infinite robustness is detected. {} {}", robustness.toWord().lastSymbol(), input);
            }
        }

        query.answer(output.toWord().suffix(query.getSuffix().length()));
        return robustness.toWord().lastSymbol();
    }

    /**
     * Inserts the robustness values of the prefixes of an executed word. This is called by the owner.
     */
    void insert(Word<String> abstractInput, Word<Double> robustness) {
        robustnessCache.insert(abstractInput, robustness);
    }
}
