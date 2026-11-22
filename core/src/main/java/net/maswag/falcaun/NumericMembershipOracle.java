package net.maswag.falcaun;

import de.learnlib.exception.SULException;
import de.learnlib.oracle.MembershipOracle;
import de.learnlib.query.Query;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.function.Function;

/**
 * The membership oracle for a {@link NumericSUL}.
 * <p>
 * This class is the single owner of the full-word executions of the SUL for membership queries and for the
 * robustness-based equivalence oracles. It maintains the following caches.
 * <ul>
 *     <li>The <em>abstract-output cache</em> maps an abstract input word to the abstract output word. It is
 *     independent of the properties.</li>
 *     <li>For each cost function registered by {@link #registerCostFunction(Function)}, the corresponding
 *     {@link RobustnessOracle} has a <em>robustness cache</em> mapping an abstract input word to the robustness
 *     values of its prefixes.</li>
 * </ul>
 * When the SUL is executed for an abstract input word, the abstract output and the prefix-wise robustness values
 * for all the registered cost functions are computed from the concrete trace, and then the concrete trace is
 * discarded. Thus, a cost function registered after the execution of a word requires another execution of the word:
 * an abstract output is not sufficient to compute the robustness.
 * <p>
 * The SUL is not executed for a word whose abstract output is cached, unless a robustness value is requested for it
 * and not cached.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public class NumericMembershipOracle implements MembershipOracle.MealyMembershipOracle<String, String> {
    private final NumericSUL sul;
    private final SignalDiscretizer discretizer;
    private final IncrementalMealyTreeBuilder<String, String> outputCache;
    private final List<RobustnessOracle> robustnessOracles = new ArrayList<>();

    public NumericMembershipOracle(NumericSUL sul, SignalDiscretizer discretizer) {
        this.sul = sul;
        this.discretizer = discretizer;
        this.outputCache = new IncrementalMealyTreeBuilder<>(discretizer.constructAbstractAlphabet());
    }

    /** {@inheritDoc} */
    @Override
    public void processQueries(Collection<? extends Query<String, Word<String>>> queries) {
        for (Query<String, Word<String>> q : queries) {
            WordBuilder<String> output = new WordBuilder<>(q.getInput().size());
            Word<String> abstractOutput = lookup(q.getInput(), output) ? output.toWord() : execute(q.getInput());
            q.answer(abstractOutput.suffix(q.getSuffix().length()));
        }
    }

    /**
     * Registers a cost function and returns the oracle computing its robustness values.
     * The robustness values are computed for each execution of the SUL after the registration.
     *
     * @param costFunc the cost function, typically an STL formula
     * @return the oracle computing the robustness values for {@code costFunc}
     */
    RobustnessOracle registerCostFunction(Function<IOSignal<List<Double>>, Double> costFunc) {
        RobustnessOracle oracle = new RobustnessOracle(this, costFunc, discretizer.constructAbstractAlphabet());
        robustnessOracles.add(oracle);
        return oracle;
    }

    /**
     * Looks up the abstract-output cache.
     *
     * @return {@code true} if and only if the abstract output for {@code abstractInput} is cached.
     */
    boolean lookup(Word<String> abstractInput, WordBuilder<String> output) {
        output.clear();
        return outputCache.lookup(abstractInput, output);
    }

    /**
     * Executes the SUL for an abstract input word and updates the abstract-output cache and the robustness caches.
     *
     * @param abstractInput the abstract input word
     * @return the abstract output word
     * @throws SULException if the execution of the SUL fails
     */
    Word<String> execute(Word<String> abstractInput) {
        final Word<List<Double>> concreteInput = discretizer.mapInput(abstractInput);
        final IOSignal<List<Double>> trace;
        try {
            trace = sul.execute(concreteInput);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw executionFailure(abstractInput, concreteInput, e);
        } catch (ExecutionException | RuntimeException e) {
            throw executionFailure(abstractInput, concreteInput, e);
        }
        assert trace.size() == abstractInput.size();

        final Word<String> abstractOutput = Word.fromList(trace.stream().map(discretizer::mapOutput).toList());
        outputCache.insert(abstractInput, abstractOutput);
        for (RobustnessOracle oracle : robustnessOracles) {
            oracle.insert(abstractInput, prefixRobustness(trace, oracle.getCostFunc()));
        }
        return abstractOutput;
    }

    /**
     * Computes the robustness values of the non-empty prefixes of a concrete trace.
     * The cost function is applied to the concrete signals including the derived signals.
     */
    private Word<Double> prefixRobustness(IOSignal<List<Double>> trace, Function<IOSignal<List<Double>>, Double> costFunc) {
        // The first element of the prefixes is the empty prefix
        return Word.fromList(trace.prefixes(false).stream().skip(1)
                .map(prefix -> new IODiscreteSignal<>(prefix.getInputSignal(),
                        Word.fromList(prefix.stream().map(discretizer::mapConcrete).toList())))
                .map(costFunc).toList());
    }

    private static SULException executionFailure(Word<String> abstractInput, Word<List<Double>> concreteInput, Exception cause) {
        return new SULException(new IllegalStateException(
                "Failed to execute numeric SUL for abstract input " + abstractInput
                        + " mapped to concrete input " + concreteInput, cause));
    }
}
