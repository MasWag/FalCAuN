package org.group_mmm;

import de.learnlib.api.query.DefaultQuery;
import net.automatalib.automata.transducers.MealyMachine;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import org.slf4j.LoggerFactory;
import org.uma.jmetal.problem.impl.AbstractIntegerProblem;
import org.uma.jmetal.solution.IntegerSolution;

import java.util.Collections;
import java.util.List;
import java.util.Objects;

public class EQSearchProblem extends AbstractIntegerProblem {
    private static final org.slf4j.Logger LOGGER = LoggerFactory.getLogger(EQSearchProblem.class);
    private List<? extends String> symbolList;
    private SimulinkMembershipOracleCost memOracle;
    private MealyMachine<?, String, ?, String> hypothesis;
    private int length;
    private DefaultQuery<String, Word<String>> cexQuery;
    private boolean stopped = false;

    EQSearchProblem(SimulinkMembershipOracleCost memOracle, int length) {
        this.memOracle = memOracle;
        this.length = length;
        setNumberOfVariables(length);
        setNumberOfObjectives(1);
        setName("EQSearchProblem");

        List<Integer> lowerLimit = Collections.nCopies(length, 0);

        setLowerLimit(lowerLimit);
    }

    void setSymbolList(List<? extends String> symbolList) {
        List<Integer> upperLimit = Collections.nCopies(length, symbolList.size() - 1);

        this.symbolList = symbolList;
        setUpperLimit(upperLimit);
    }

    @Override
    public void evaluate(IntegerSolution integerSolution) {
        WordBuilder<String> currentSample = new WordBuilder<>();
        for (int i = 0; i < integerSolution.getNumberOfVariables(); i++) {
            int value = integerSolution.getVariableValue(i);
            currentSample.append(symbolList.get(value));
        }
        DefaultQuery<String, Word<String>> query = new DefaultQuery<>(currentSample.toWord());
        double robustness = memOracle.processQueryWithCost(query);
        integerSolution.setObjective(0, robustness);
        LOGGER.debug("Robustness: {}", robustness);
        Word<String> hypOutput = hypothesis.computeOutput(query.getInput());
        if (!Objects.equals(hypOutput, query.getOutput())) {
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
