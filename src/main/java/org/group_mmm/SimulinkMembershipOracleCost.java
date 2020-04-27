package org.group_mmm;

import de.learnlib.api.query.Query;
import net.automatalib.incremental.mealy.IncrementalMealyBuilder;
import net.automatalib.incremental.mealy.tree.IncrementalMealyTreeBuilder;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

class SimulinkMembershipOracleCost extends SimulinkMembershipOracle {
    private static final Logger LOGGER = LoggerFactory.getLogger(SimulinkMembershipOracleCost.class);
    private IncrementalMealyBuilder<String, Double> costCache;
    private Function<Word<List<Double>>, Double> costFunc;
    private Set<SimulinkMembershipOracleCost> notifiedSet = new HashSet<>();

    SimulinkMembershipOracleCost(SimulinkSUL simulink, SimulinkSULMapper mapper, Function<Word<List<Double>>, Double> costFunc) {
        super(simulink, mapper);
        this.costFunc = costFunc;
        this.costCache = new IncrementalMealyTreeBuilder<>(mapper.constructAbstractAlphabet());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void processQueries(Collection<? extends Query<String, Word<String>>> queries) {
        for (Query<String, Word<String>> q : queries) {
            final Word<String> abstractInput = q.getInput();
            WordBuilder<String> abstractOutputBuilder = new WordBuilder<>(abstractInput.size());

            if (!cache.lookup(abstractInput, abstractOutputBuilder)) {
                processQueryWithCost(q);
            } else {
                final Word<String> output = abstractOutputBuilder.toWord().suffix(q.getSuffix().length());
                q.answer(output);
            }
        }
    }

    Double processQueryWithCost(Query<String, Word<String>> q) {
        final Word<String> abstractInput = q.getInput();
        WordBuilder<String> abstractOutputBuilder = new WordBuilder<>(abstractInput.size());
        WordBuilder<Double> costBuilder = new WordBuilder<>(abstractInput.size());

        if (!cache.lookup(abstractInput, abstractOutputBuilder) || !costCache.lookup(abstractInput, costBuilder) || costBuilder.toWord().lastSymbol().isInfinite()) {
            abstractOutputBuilder.clear();
            costBuilder.clear();

            final Word<List<Double>> concreteInput = Word.fromList(
                    abstractInput.stream().map(mapper::mapInput).collect(Collectors.toList()));

            final Word<List<Double>> concreteOutput;
            try {
                concreteOutput = simulink.execute(concreteInput);
            } catch (Exception e) {
                LOGGER.error(e.getMessage());
                return null;
            }
            assert concreteOutput.size() == concreteInput.size();
            List<Double> robustness = concreteOutput.prefixes(false).stream().map(costFunc).collect(Collectors.toList());
            costBuilder.append(robustness);

            abstractOutputBuilder.append(
                    concreteOutput.stream().map(mapper::mapOutput).collect(Collectors.toList()));

            assert concreteOutput.size() == abstractOutputBuilder.toWord().size();

            cache.insert(abstractInput, abstractOutputBuilder.toWord());
            costCache.insert(abstractInput, costBuilder.toWord());
            // for assert
            WordBuilder<Double> tmpCostBuilder = new WordBuilder<>(abstractInput.size());
            costCache.lookup(abstractInput, tmpCostBuilder);
            assert (Objects.equals(tmpCostBuilder.toWord(), costBuilder.toWord()));
            for (SimulinkMembershipOracleCost notified : notifiedSet) {
                notified.cacheInsert(abstractInput, concreteOutput, abstractOutputBuilder.toWord());
            }
            costCache.lookup(abstractInput, tmpCostBuilder);
            assert (Objects.equals(tmpCostBuilder.toWord(), costBuilder.toWord()));
            if (costBuilder.toWord().lastSymbol().isInfinite()) {
                LOGGER.warn("Infinite robustness is detected. {} {}", costBuilder.toWord().lastSymbol(), abstractInput);
                LOGGER.warn("Raw Output: {}", concreteOutput);
            }
        }

        final Word<String> output = abstractOutputBuilder.toWord().suffix(q.getSuffix().length());
        q.answer(output);
        return costBuilder.toWord().lastSymbol();
    }

    private void cacheInsert(Word<String> abstractInput, Word<List<Double>> concreteOutput, Word<String> abstractOutput) {
        super.cacheInsert(abstractInput, abstractOutput);
        WordBuilder<Double> costBuilder = new WordBuilder<>(abstractInput.size());
        List<Double> robustness = concreteOutput.prefixes(false).stream().map(costFunc).collect(Collectors.toList());
        costBuilder.append(robustness);
        costCache.insert(abstractInput, costBuilder.toWord());
    }

    boolean addNotified(SimulinkMembershipOracleCost notified) {
        return notifiedSet.add(notified);
    }

    boolean addNotifiedAll(Collection<SimulinkMembershipOracleCost> notified) {
        return notifiedSet.addAll(notified);
    }
}
