package org.group_mmm;

import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.api.query.Query;
import net.automatalib.words.Word;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.Collection;
import java.util.stream.Collectors;

/**
 * The membership oracle for a Simulink model
 */
public class SimulinkMembershipOracle implements MembershipOracle.MealyMembershipOracle<String, String> {
    private static final Logger LOGGER = LoggerFactory.getLogger(SimulinkMembershipOracle.class);

    private SimulinkSUL simulink;
    private SimulinkSULMapper mapper;

    SimulinkMembershipOracle(SimulinkSUL simulink, SimulinkSULMapper mapper) {
        this.simulink = simulink;
        this.mapper = mapper;
    }

    @Override
    public void processQueries(Collection<? extends Query<String, Word<String>>> queries) {
        for (Query<String, Word<String>> q : queries) {
            final Word<ArrayList<Double>> concreteInput = Word.fromList(
                    q.getInput().stream().map(mapper::mapInput).collect(Collectors.toList()));
            assert concreteInput.size() == q.getInput().size();

            final Word<ArrayList<Double>> concreteOutput;
            try {
                concreteOutput = simulink.execute(concreteInput);
            } catch (Exception e) {
                LOGGER.error(e.getMessage());
                return;
            }
            assert concreteOutput.size() == concreteInput.size();
            final Word<String> abstractOutput = Word.fromList(
                    concreteOutput.stream().map(mapper::mapOutput).collect(Collectors.toList()));
            assert concreteOutput.size() == abstractOutput.size();

            final Word<String> output = abstractOutput.suffix(q.getSuffix().length());
            q.answer(output);
        }
    }
}

