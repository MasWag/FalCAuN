package org.group_mmm;

import net.automatalib.incremental.mealy.IncrementalMealyBuilder;
import net.automatalib.incremental.mealy.dag.IncrementalMealyDAGBuilder;
import net.automatalib.ts.output.MealyTransitionSystem;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;

class TreeCache<In, Out> {
    private final TreeCacheImpl<?, In, ?, Out> impl;

    TreeCache(Alphabet<In> inputAlphabet) {
        IncrementalMealyBuilder<In, Out> incMealy = new IncrementalMealyDAGBuilder<>(inputAlphabet);
        impl = new TreeCacheImpl<>(incMealy, incMealy.asTransitionSystem());
    }

    Word<Out> get(Word<In> input) {
        return impl.get(input);
    }

    void put(Word<In> input, Word<Out> output) {
        impl.put(input, output);
    }

    private class TreeCacheImpl<S, I, T, O> {
        private final IncrementalMealyBuilder<I, O> incMealy;
        private final MealyTransitionSystem<S, I, T, O> mealyTs;

        TreeCacheImpl(IncrementalMealyBuilder<I, O> incMealy,
                      MealyTransitionSystem<S, I, T, O> mealyTs) {
            this.incMealy = incMealy;
            this.mealyTs = mealyTs;
        }

        Word<O> get(Word<I> input) {
            WordBuilder<O> builder = new WordBuilder<>();

            if (input.isEmpty()) {
                return Word.epsilon();
            }
            S current = mealyTs.getInitialState();

            for (final I in : input) {
                if (current == null) {
                    return null;
                }
                T trans = mealyTs.getTransition(current, in);

                if (trans == null) {
                    return null;
                }
                builder.append(mealyTs.getTransitionOutput(trans));
                current = mealyTs.getSuccessor(trans);
            }
            return builder.toWord();
        }

        void put(Word<I> input, Word<O> output) {
            assert input.size() == output.size();
            if (input.isEmpty()) {
                return;
            }
            incMealy.insert(input, output);
        }
    }
}
