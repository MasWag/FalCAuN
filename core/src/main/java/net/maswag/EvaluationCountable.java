package net.maswag;

import de.learnlib.oracle.PropertyOracle;

import java.util.ArrayList;

public interface EvaluationCountable {
    int getEvaluateCount();

    interface MealyEquivalenceOracle<I, O> extends EvaluationCountable, PropertyOracle.MealyEquivalenceOracle<I, O> {
    }

    class Sum extends ArrayList<EvaluationCountable> implements EvaluationCountable {
        public int getEvaluateCount() {
            return stream().mapToInt(EvaluationCountable::getEvaluateCount).sum();
        }
    }
}
