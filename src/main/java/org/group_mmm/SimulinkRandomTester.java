package org.group_mmm;

import de.learnlib.api.SUL;
import de.learnlib.filter.cache.sul.SULCache;
import de.learnlib.mapper.MappedSUL;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import org.slf4j.LoggerFactory;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

/**
 * Pure Random Tester of a Simulink model
 *
 * @author Masaki Waga <masaki@gmail.com>
 */
public class SimulinkRandomTester {
    protected SUL<List<Double>, List<Double>> simulink;
    private SimulinkSUL rawSimulink;
    private Alphabet<String> abstractInputAlphabet;
    private Alphabet<List<Double>> concreteInputAlphabet;
    private SimulinkSULMapper mapper;
    private SUL<String, String> mappedSimulink;
    private List<STLCost> costFunc;
    private long timeout;
    private List<Word<String>> cexInput;
    private List<String> cexProperty;
    private List<Word<String>> cexOutput;
    private int length;
    private Random random = new Random();
    private List<String> properties;
    private static final org.slf4j.Logger LOGGER = LoggerFactory.getLogger(SimulinkRandomTester.class);


    /**
     * @param initScript The MATLAB script called at first. You have to define mdl in the script.
     * @param paramName  The list of input parameters.
     * @param length     The length of the sampled signals.
     * @param signalStep The signal step in the simulation
     * @param properties The LTL properties to be verified
     * @param costFunc   The STL properties to be verified
     * @param mapper     The I/O mapepr between abstract/concrete Simulink models.
     * @throws Exception It can be thrown from the constructor of SimulinkSUL.
     */
    public SimulinkRandomTester(String initScript, List<String> paramName, int length, double signalStep, List<String> properties, List<STLCost> costFunc, SimulinkSULMapper mapper) throws Exception {
        this.mapper = mapper;
        this.rawSimulink = new SimulinkSUL(initScript, paramName, signalStep);
        this.concreteInputAlphabet = mapper.constructConcreteAlphabet();
        this.abstractInputAlphabet = mapper.constructAbstractAlphabet();

        this.properties = properties;

        this.simulink = SULCache.createTreeCache(this.concreteInputAlphabet, rawSimulink);
        this.length = length;
        this.mappedSimulink = new MappedSUL<>(mapper, simulink);
        this.mappedSimulink = SULCache.createTreeCache(this.abstractInputAlphabet, this.mappedSimulink);
        this.costFunc = costFunc;
        assert (costFunc.size() == properties.size());
    }

    /**
     * Set timeout to the equivalence oracle added next time.
     *
     * @param timeout timeout in seconds.
     */
    void setTimeout(long timeout) {
        this.timeout = timeout;
    }

    List<Word<String>> getCexAbstractInput() {
        return cexInput;
    }

    List<Word<List<Double>>> getCexConcreteInput() {
        return this.mapper.mapInputs(getCexAbstractInput());
    }


    List<Word<String>> getCexOutput() {
        return cexOutput;
    }

    List<String> getCexProperty() {
        return cexProperty;
    }

    /**
     * @return Returns {@code true} if and only if the Simulink model is verified i.e., no counter example is found.
     */
    public boolean run() {
        cexInput = new ArrayList<>();
        cexOutput = new ArrayList<>();
        cexProperty = new ArrayList<>();
        long nanoTimeout = timeout * 1000000000;
        List<Integer> unfalsifiedIndex = IntStream.range(0, this.properties.size()).boxed().collect(Collectors.toList());
        long startTime = System.nanoTime();
        while ((System.nanoTime() - startTime) <= nanoTimeout) {
            Word<String> abstractInput = generateTestWord(new ArrayList<>(abstractInputAlphabet));

            final Word<List<Double>> concreteInput = Word.fromList(
                    abstractInput.stream().map(mapper::mapInput).collect(Collectors.toList()));

            try {
                Word<List<Double>> concreteOutput = this.rawSimulink.execute(concreteInput);
                LOGGER.debug("Abstract input: " + abstractInput);
                LOGGER.debug("Concrete output: " + concreteOutput);
                Iterator<Integer> it = unfalsifiedIndex.iterator();
                while (it.hasNext()) {
                    int i = it.next();
                    LOGGER.debug("Robustness: " + costFunc.get(i).apply(concreteOutput));
                    if (costFunc.get(i).apply(concreteOutput) < 0) {
                        LOGGER.info("Property_violated: " + properties.get(i));
                        LOGGER.info("Counter example for property: " + abstractInput);
                        LOGGER.info("Concrete output: " + concreteOutput);
                        LOGGER.info("Robustness: " + costFunc.get(i).apply(concreteOutput));

                        cexInput.add(abstractInput);
                        cexProperty.add(properties.get(i));
                        cexOutput.add(Word.fromList(
                                concreteOutput.stream().map(mapper::mapOutput).collect(Collectors.toList())));
                        it.remove();
                        LOGGER.debug("cexInput size: " + cexInput.size());
                    }
                }
            } catch (Exception e) {
                LOGGER.error(e.getMessage());
            }
        }
        return cexProperty.isEmpty();
    }

    /**
     * Generate one word of length {@code length} randomly
     *
     * @param symbolList The list of the possible symbols
     * @return the generated word
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
}
