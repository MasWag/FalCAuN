package net.maswag;

import de.learnlib.oracle.EquivalenceOracle;
import de.learnlib.oracle.MembershipOracle;
import de.learnlib.oracle.PropertyOracle;
import de.learnlib.query.DefaultQuery;
import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.word.Word;

import javax.annotation.Nullable;
import javax.annotation.ParametersAreNonnullByDefault;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Objects;

/**
 * Equivalence oracle that uses a fixed set of samples.
 */
@Slf4j
public class MealyFixedSetEQOracle implements EquivalenceOracle.MealyEquivalenceOracle<String, String>, EvaluationCountable. MealyEquivalenceOracle<String, String> {
    List<Word<String>> fixedSamples = new ArrayList<>();
    private final List<PropertyOracle.MealyPropertyOracle<String, String, String>> ltlOracles;
    protected final MembershipOracle.MealyMembershipOracle<String, String> memOracle;
    @Getter
    protected int evaluateCount = 0;

    /**
     * Constructor for MealyFixedSetEQOracle.
     *
     * @param ltlOracles the list of LTL oracles so that we stop if all of them are disproved.
     * @param memOracle  the membership oracle used to test the equivalence.
     */
    public MealyFixedSetEQOracle(List<PropertyOracle.MealyPropertyOracle<String, String, String>> ltlOracles,
                                 MembershipOracle.MealyMembershipOracle<String, String> memOracle) {
        this.ltlOracles = ltlOracles;
        this.memOracle = memOracle;
    }

    public void add(Word<String> sample) {
        fixedSamples.add(sample);
    }

    public void addAll(Collection<Word<String>> samples) {
        fixedSamples.addAll(samples);
    }

    /**
     * Returns whether the property is disproved i.e., whether it observed such an input that the cost function {@literal < 0}.
     *
     * @return whether the property is disproved.
     */
    private boolean isDisproved() {
        return ltlOracles != null && ltlOracles.stream().allMatch(PropertyOracle::isDisproved);
    }

    /**
     * {@inheritDoc}
     */
    @Nullable
    @ParametersAreNonnullByDefault
    @Override
    public DefaultQuery<String, Word<String>> findCounterExample(MealyMachine<?, String, ?, String> hypothesis, Collection<? extends String> inputs) {
        if (isDisproved()) {
            log.debug("A counterexample is already found!!");
            return null;
        }
        // Fail fast on empty inputs
        if (inputs.isEmpty()) {
            log.warn("Passed empty set of inputs to equivalence oracle; no counterexample can be found!");
            return null;
        }

        // Evaluate fixed inputs
        for (Word<String> sample : fixedSamples) {
            DefaultQuery<String, Word<String>> query = new DefaultQuery<>(sample);
            memOracle.processQuery(query);
            evaluateCount++;
            Word<String> hypOutput = hypothesis.computeOutput(query.getInput());
            log.trace("Processing fixed sample: {}", sample);
            log.trace("Query: {}", query);
            log.trace("Hypothesis output: {}", hypOutput);
            if (!Objects.equals(hypOutput, query.getOutput())) {
                log.debug("A counterexample is found with: {}", query);
                return query;
            }
        }

        log.debug("No counterexample found in the fixed set of samples.");
        return null;
    }
}
