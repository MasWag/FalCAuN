package net.maswag.falcaun;

import de.learnlib.query.DefaultQuery;
import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;
import org.uma.jmetal.problem.integerproblem.impl.AbstractIntegerProblem;
import org.uma.jmetal.solution.integersolution.IntegerSolution;
import org.uma.jmetal.util.bounds.Bounds;

import java.util.Collections;
import java.util.List;
import java.util.Objects;

/**
 * <p>EQSearchProblem class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class EQSearchProblem extends AbstractIntegerProblem implements EvaluationCountable {
    private List<? extends String> symbolList;
    private final NumericMembershipOracleCost memOracle;
    private MealyMachine<?, String, ?, String> hypothesis;
    private final int length;
    private DefaultQuery<String, Word<String>> cexQuery;
    private boolean stopped = false;
    @Getter
    private int evaluateCount = 0;

    EQSearchProblem(NumericMembershipOracleCost memOracle, int length) {
        this.memOracle = memOracle;
        this.length = length;
        numberOfObjectives(1);
        name("EQSearchProblem");

        // The solutions share these bounds, so the upper bound follows the latest symbol list even for a reused population.
        bounds = Collections.nCopies(length, new Bounds<>() {
            @Override
            public Integer getLowerBound() {
                return 0;
            }

            @Override
            public Integer getUpperBound() {
                return Objects.isNull(symbolList) ? 0 : symbolList.size() - 1;
            }
        });
    }

    void setSymbolList(List<? extends String> symbolList) {
        this.symbolList = symbolList;
    }

    /** {@inheritDoc} */
    @Override
    public IntegerSolution evaluate(IntegerSolution integerSolution) {
        WordBuilder<String> currentSample = new WordBuilder<>();
        for (int i = 0; i < integerSolution.variables().size(); i++) {
            int value = integerSolution.variables().get(i);
            currentSample.append(symbolList.get(value));
        }
        DefaultQuery<String, Word<String>> query = new DefaultQuery<>(currentSample.toWord());
        int oldCount = memOracle.getEvaluateCount();
        double robustness = memOracle.processQueryWithCost(query);
        evaluateCount += memOracle.getEvaluateCount() - oldCount;
        integerSolution.objectives()[0] = robustness;
        log.trace("Robustness: {}", robustness);
        Word<String> hypOutput = hypothesis.computeOutput(query.getInput());
        if (!Objects.equals(hypOutput, query.getOutput())) {
            log.debug("CEX with Robustness: {}", robustness);
            stopped = true;
            cexQuery = query;
        }
        return integerSolution;
    }

    DefaultQuery<String, Word<String>> getCexQuery() {
        return cexQuery;
    }

    void setHypothesis(MealyMachine<?, String, ?, String> hypothesis) {
        this.hypothesis = hypothesis;
        stopped = false;
    }

    boolean isStopped() {
        return stopped;
    }
}
