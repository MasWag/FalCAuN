package net.maswag.falcaun;

import java.util.Collection;

import de.learnlib.oracle.PropertyOracle;
import de.learnlib.query.DefaultQuery;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.util.automaton.equivalence.DeterministicEquivalenceTest;
import net.automatalib.word.Word;


public class WhiteBoxEqOracle implements PropertyOracle.MealyEquivalenceOracle<String, String> {
  MealyMachine<?, String, ?, String> targetMealy;

  public WhiteBoxEqOracle(MealyMachine<?, String, ?, String> target) {
    this.targetMealy = target;
  }

  public DefaultQuery<String, Word<String>> findCounterExample(MealyMachine<?, String, ?, String> hypothesisMealy, Collection<? extends String> sigma) {
    Word<String> cexInput = DeterministicEquivalenceTest.findSeparatingWord(targetMealy, hypothesisMealy, sigma);
    if (cexInput == null) return null;
    Word<String> cexOutput = targetMealy.computeOutput(cexInput);
    DefaultQuery<String, Word<String>> refinementQuery = new DefaultQuery<>(Word.epsilon(), cexInput, cexOutput);
    return refinementQuery;
  }
}