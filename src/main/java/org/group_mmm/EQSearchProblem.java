package org.group_mmm;

import de.learnlib.api.query.DefaultQuery;
import lombok.Getter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.automata.transducers.MealyMachine;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import org.uma.jmetal.problem.integerproblem.impl.AbstractIntegerProblem;
import org.uma.jmetal.solution.integersolution.IntegerSolution;

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
    private final SimulinkMembershipOracleCost memOracle;
    private MealyMachine<?, String, ?, String> hypothesis;
    private final int length;
    private DefaultQuery<String, Word<String>> cexQuery;
    private boolean stopped = false;
    @Getter
    private int evaluateCount = 0;

    EQSearchProblem(SimulinkMembershipOracleCost memOracle, int length) {
        this.memOracle = memOracle;
        this.length = length;
        setNumberOfVariables(length);
        setNumberOfObjectives(1);
        setName("EQSearchProblem");

        List<Integer> lowerLimit = Collections.nCopies(length, 0);
        List<Integer> upperLimit = Collections.nCopies(length, Integer.MAX_VALUE);

        setVariableBounds(lowerLimit, upperLimit);
    }

    void setSymbolList(List<? extends String> symbolList) {
        List<Integer> lowerLimit = Collections.nCopies(length, 0);
        List<Integer> upperLimit = Collections.nCopies(length, symbolList.size() - 1);

        this.symbolList = symbolList;
        setVariableBounds(lowerLimit, upperLimit);
    }

    /** {@inheritDoc} */
    @Override
    public void evaluate(IntegerSolution integerSolution) {
        WordBuilder<String> currentSample = new WordBuilder<>();
        for (int i = 0; i < integerSolution.getNumberOfVariables(); i++) {
            int value = integerSolution.getVariables().get(i);
            currentSample.append(symbolList.get(value));
        }
        DefaultQuery<String, Word<String>> query = new DefaultQuery<>(currentSample.toWord());
        int oldCount = memOracle.getEvaluateCount();
        double robustness = memOracle.processQueryWithCost(query);
        evaluateCount += memOracle.getEvaluateCount() - oldCount;
        integerSolution.setObjective(0, robustness);
        log.trace("Robustness: {}", robustness);
        Word<String> hypOutput = hypothesis.computeOutput(query.getInput());
        if (!Objects.equals(hypOutput, query.getOutput())) {
            log.info("CEX with Robustness: {}", robustness);
            stopped = true;
            cexQuery = query;
        }
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
