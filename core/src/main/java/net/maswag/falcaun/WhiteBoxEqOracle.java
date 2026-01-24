package net.maswag.falcaun;

import java.util.Collection;

import de.learnlib.oracle.PropertyOracle;
import de.learnlib.oracle.equivalence.MealySimulatorEQOracle;
import de.learnlib.query.DefaultQuery;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.util.automaton.equivalence.DeterministicEquivalenceTest;
import net.automatalib.word.Word;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Equivalence Oracle using the actual model of SUL.
 * <p>
 * This class provides equivalence oracle based on the difference of two (white-box) Mealy machines.
 *
 * @author Tsubasa Matsumoto {@literal <tsubari96061@gmail.com>}
 */
public class WhiteBoxEqOracle implements PropertyOracle.MealyEquivalenceOracle<String, String> {

    private static final Logger LOG = LoggerFactory.getLogger(WhiteBoxEqOracle.class);

    private final MealyMachine<?, String, ?, String> targetMealy;
    private final MealySimulatorEQOracle<String, String> fallbackOracle;

    public WhiteBoxEqOracle(MealyMachine<?, String, ?, String> target) {
        this.targetMealy = target;
        this.fallbackOracle = new MealySimulatorEQOracle<>(target);
    }

    @Override
    public DefaultQuery<String, Word<String>> findCounterExample(MealyMachine<?, String, ?, String> hypothesisMealy,
                                                                 Collection<? extends String> sigma) {
        try {
            Word<String> cexInput = DeterministicEquivalenceTest.findSeparatingWord(targetMealy, hypothesisMealy, sigma);
            if (cexInput == null) {
                return null;
            }
            Word<String> cexOutput = targetMealy.computeOutput(cexInput);
            return new DefaultQuery<>(Word.epsilon(), cexInput, cexOutput);
        } catch (ArrayIndexOutOfBoundsException ex) {
            LOG.warn("AutomataLib separation failed, falling back to simulator equivalence oracle", ex);
            return fallbackOracle.findCounterExample(hypothesisMealy, sigma);
        }
    }
}
