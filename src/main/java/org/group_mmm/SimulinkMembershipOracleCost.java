package org.group_mmm;

import de.learnlib.api.query.Query;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.function.Function;
import java.util.stream.Collectors;

class SimulinkMembershipOracleCost extends SimulinkMembershipOracle {
    private static final Logger LOGGER = LoggerFactory.getLogger(SimulinkMembershipOracleCost.class);
    private IncrementalMealyTreeBuilder<String, Double> costCache;
    private Function<Word<ArrayList<Double>>, Double> costFunc;

    IncrementalMealyTreeBuilder<String, Double> getCostCache() {
        return costCache;
    }

    void setCostCache(IncrementalMealyTreeBuilder<String, Double> costCache) {
        this.costCache = costCache;
    }

    SimulinkMembershipOracleCost(SimulinkSUL simulink, SimulinkSULMapper mapper, Function<Word<ArrayList<Double>>, Double> costFunc) {
        super(simulink, mapper);
        this.costFunc = costFunc;
        this.costCache = new IncrementalMealyTreeBuilder<>(mapper.constructAbstractAlphabet());

    }

    Double processQueryWithCost(Query<String, Word<String>> q) {
        final Word<String> abstractInput = q.getInput();
        WordBuilder<String> abstractOutputBuilder = new WordBuilder<>(abstractInput.size());
        WordBuilder<Double> costBuilder = new WordBuilder<>(abstractInput.size());

        if (!cache.lookup(abstractInput, abstractOutputBuilder)) {
            abstractOutputBuilder.clear();
            costBuilder.clear();

            final Word<ArrayList<Double>> concreteInput = Word.fromList(
                    abstractInput.stream().map(mapper::mapInput).collect(Collectors.toList()));

            final Word<ArrayList<Double>> concreteOutput;
            try {
                concreteOutput = simulink.execute(concreteInput);
            } catch (Exception e) {
                LOGGER.error(e.getMessage());
                return null;
            }
            assert concreteOutput.size() == concreteInput.size();
            costBuilder.append(
                    concreteOutput.prefixes(false).
                            stream().map(costFunc).collect(Collectors.toList()));

            abstractOutputBuilder.append(
                    concreteOutput.stream().map(mapper::mapOutput).collect(Collectors.toList()));

            assert concreteOutput.size() == abstractOutputBuilder.toWord().size();
            cache.insert(abstractInput, abstractOutputBuilder.toWord());
            costCache.insert(abstractInput, costBuilder.toWord());
        } else {
            costCache.lookup(abstractInput, costBuilder);
        }

        final Word<String> output = abstractOutputBuilder.toWord().suffix(q.getSuffix().length());
        q.answer(output);
        return costBuilder.toWord().lastSymbol();
    }
}
