package net.maswag.falcaun;

import com.google.common.collect.SortedSetMultimap;
import com.google.common.collect.TreeMultimap;
import de.learnlib.oracle.EquivalenceOracle;
import de.learnlib.oracle.PropertyOracle;
import de.learnlib.query.DefaultQuery;
import lombok.Getter;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import org.jetbrains.annotations.Nullable;
import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.primitives.Doubles.min;

/**
 * Abstract class for implementing equivalence oracles that select test cases based on a cost function.
 * This class serves as a foundational framework for generating and evaluating test cases aimed at finding
 * counterexamples in Mealy machines. It is designed to be extended by specific implementations that define
 * the logic for selecting test cases and evaluating their costs.
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
public abstract class AbstractSelectEQOracle implements EquivalenceOracle.MealyEquivalenceOracle<String, String>,
        EvaluationCountable.MealyEquivalenceOracle<String, String> {
    /**
     * Logger instance for this class, used for logging debug and error information during the execution of the equivalence oracle.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(AbstractSelectEQOracle.class);

    /**
     * Random number generator used for generating random test cases to ensure diversity in the test suite.
     */
    protected Random random;

    /**
     * The number of initial test cases generated to start the evaluation process. This parameter determines the diversity and coverage of the initial set of test cases.
     */
    protected int generationSize;

    /**
     * The number of child test cases generated from each successful (good) sample. This parameter controls the diversity and depth of the test case generation process.
     */
    protected int childrenSize;

    /**
     * A list containing all possible input symbols that can be used in the test cases. This list defines the alphabet of inputs for the Mealy machine being tested.
     */
    protected List<? extends String> symbolList;

    /**
     * The membership oracle responsible for evaluating the generated test cases against the Mealy machine. It provides the cost associated with each test case and determines whether it is a counterexample.
     */
    protected NumericMembershipOracleCost memOracle;

    /**
     * The length of each generated test word. This parameter defines how long each test case will be, affecting the complexity and coverage of the tests.
     */
    private int length;

    /**
     * The maximum number of test cases to evaluate before terminating the search for counterexamples. This parameter prevents infinite loops and ensures that the process does not run indefinitely.
     */
    private int maxTests;

    /**
     * A flag that indicates whether the word generation process should be reset. If set to true, it will clear and regenerate the initial set of test cases.
     */
    protected boolean resetWord;

    /**
     * A list containing the current set of test cases that are being evaluated. This list is updated as new generations of test cases are generated and evaluated.
     */
    private List<Word<String>> currentSamples = new ArrayList<>(generationSize);

    /**
     * The property oracle responsible for checking whether a specific property (e.g., an LTL formula) is disproved by the generated test cases. If provided, it overrides the cost-based evaluation mechanism.
     */
    private PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle;

    /**
     * A counter that keeps track of the total number of test cases evaluated during the search process. This helps in monitoring the progress and performance of the equivalence oracle.
     */
    @Getter
    private int evaluateCount = 0;

    /**
     * Constructs an instance of {@code AbstractSelectEQOracle} with the specified parameters. This constructor initializes the equivalence oracle without a property oracle, relying solely on the cost function provided by the membership oracle to evaluate test cases.
     *
     * @param memOracle      The membership oracle used to evaluate test cases and provide costs.
     * @param length         The length of each generated test word.
     * @param random         Random number generator for generating diverse test cases.
     * @param maxTests       Maximum number of test cases to evaluate before terminating the search process.
     * @param generationSize Size of the initial set of test cases generated at the start.
     * @param childrenSize   Number of child test cases generated from each successful (good) sample.
     * @param resetWord      Flag indicating whether to reset the word generation process, clearing and regenerating the initial set of test cases if true.
     */
    AbstractSelectEQOracle(NumericMembershipOracleCost memOracle,
                           int length,
                           Random random,
                           int maxTests,
                           int generationSize,
                           int childrenSize,
                           boolean resetWord) {
        this.memOracle = memOracle;
        this.length = length;
        this.random = random;
        this.maxTests = maxTests;
        this.generationSize = generationSize;
        this.childrenSize = childrenSize;
        this.resetWord = resetWord;
    }

    /**
     * Constructs an instance of {@code AbstractSelectEQOracle} with the specified parameters, including a property oracle. This constructor initializes the equivalence oracle with both a membership oracle and a property oracle, allowing it to evaluate test cases based on both cost functions and specific properties (e.g., LTL formulas).
     *
     * @param memOracle      The membership oracle used to evaluate test cases and provide costs.
     * @param length         The length of each generated test word.
     * @param random         Random number generator for generating diverse test cases.
     * @param maxTests       Maximum number of test cases to evaluate before terminating the search process.
     * @param generationSize Size of the initial set of test cases generated at the start.
     * @param childrenSize   Number of child test cases generated from each successful (good) sample.
     * @param resetWord      Flag indicating whether to reset the word generation process, clearing and regenerating the initial set of test cases if true.
     * @param ltlOracle      The property oracle used to check if a specific property is disproved by the generated test cases. If provided, it overrides the cost-based evaluation mechanism.
     */
    AbstractSelectEQOracle(NumericMembershipOracleCost memOracle,
                           int length,
                           Random random,
                           int maxTests,
                           int generationSize,
                           int childrenSize,
                           boolean resetWord,
                           PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle) {
        this.memOracle = memOracle;
        this.length = length;
        this.random = random;
        this.maxTests = maxTests;
        this.generationSize = generationSize;
        this.childrenSize = childrenSize;
        this.resetWord = resetWord;
        this.ltlOracle = ltlOracle;
    }

    /**
     * Resets the list of current samples by clearing it and generating a new set of random test words. This method is used to refresh the initial set of test cases when necessary.
     */
    private void resetSamples() {
        currentSamples.clear();

        for (int i = 0; i < generationSize; i++) {
            currentSamples.add(generateTestWord(symbolList));
        }
    }

    /**
     * Minimum cost observed during the evaluation process.
     */
    private double minCost = Double.POSITIVE_INFINITY;

    /**
     * Checks if a property has been disproved by evaluating the minimum observed cost. If a property oracle is provided, it checks whether the property is disproved using the oracle; otherwise, it checks if the minimum observed cost is less than zero.
     *
     * @return {@code true} if the property is disproved, {@code false} otherwise.
     */
    private boolean isDisproved() {
        if (ltlOracle != null) {
            return ltlOracle.isDisproved();
        } else {
            return minCost < 0;
        }
    }

    /**
     * Finds a counterexample to the given hypothesis Mealy machine using the specified set of input symbols. This method generates and evaluates test cases to determine if there is any input that causes the hypothesis to produce an output different from the expected output.
     *
     * @param hypothesis The Mealy machine hypothesis to be tested.
     * @param inputs     A collection of possible input symbols for generating test cases.
     * @return A {@code DefaultQuery} representing a counterexample if found, or {@code null} if no counterexample is discovered within the specified constraints.
     */
    @Nullable
    @Override
    public DefaultQuery<String, Word<String>> findCounterExample(MealyMachine<?, String, ?, String> hypothesis, Collection<? extends String> inputs) {
        if (isDisproved()) {
            LOGGER.debug("A counterexample is already found!!");
            return null;
        }
        // Fail fast on empty inputs
        if (inputs.isEmpty()) {
            LOGGER.warn("Passed empty set of inputs to equivalence oracle; no counterexample can be found!");
            return null;
        }
        int testSize = 0;
        symbolList = new ArrayList<>(inputs);

        if (resetWord || currentSamples.isEmpty()) {
            resetSamples();
        }

        do {
            SortedSetMultimap<Double, Word<String>> map = TreeMultimap.create(Comparator.comparingDouble(Double::doubleValue), Comparator.comparingInt(Word::size));

            // Evaluate the current samples
            for (Word<String> sample : currentSamples) {
                DefaultQuery<String, Word<String>> query = new DefaultQuery<>(sample);
                int oldCount = memOracle.getEvaluateCount();
                Double result = memOracle.processQueryWithCost(query);
                evaluateCount += memOracle.getEvaluateCount() - oldCount;
                Word<String> hypOutput = hypothesis.computeOutput(query.getInput());
                minCost = min(result, minCost);
                if (!Objects.equals(hypOutput, query.getOutput())) {
                    return query;
                }
                if (++testSize >= maxTests) {
                    return null;
                }
                map.put(result, sample);
            }
            LOGGER.debug("Test size: {}", testSize);

            List<Word<String>> goodSamples = map.entries().stream().limit(generationSize).map(Map.Entry::getValue).collect(Collectors.toList());

            // Construct next generation
            List<Word<String>> nextSamples = createNextGeneration(goodSamples);
            if (Objects.equals(nextSamples, currentSamples)) {
                resetSamples();
            } else {
                currentSamples = nextSamples;
            }
        } while (testSize < maxTests);

        return null;
    }

    /**
     * Generates a random test word of the specified length using the provided list of possible input symbols. This method is used to create initial test cases for evaluation.
     *
     * @param symbolList A list containing all possible input symbols that can be used in the test cases.
     * @return A randomly generated {@code Word} of the specified length.
     */
    private Word<String> generateTestWord(List<? extends String> symbolList) {
        final int numSyms = symbolList.size();
        final WordBuilder<String> result = new WordBuilder<>(length);

        for (int j = 0; j < length; ++j) {
            int symidx = random.nextInt(numSyms);
            String sym = symbolList.get(symidx);
            result.append(sym);
        }

        return result.toWord();
    }

    /**
     * Generates the next set of test cases based on the provided list of successful (good) samples. This method is responsible for creating new test cases that are derived from the current set of successful samples, ensuring a diverse and evolving set of test cases.
     *
     * @param goodSamples A list of successful test cases used as the basis for generating the next generation of test cases.
     * @return A list of newly generated test cases for the next evaluation cycle.
     */
    abstract List<Word<String>> createNextGeneration(List<Word<String>> goodSamples);
}
