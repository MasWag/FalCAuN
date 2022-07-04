package org.group_mmm;

import ch.qos.logback.classic.Level;
import ch.qos.logback.classic.Logger;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.modelcheckers.ltsmin.AbstractLTSmin;
import net.automatalib.modelcheckers.ltsmin.LTSminVersion;
import net.automatalib.words.Word;
import org.apache.commons.cli.MissingOptionException;
import org.slf4j.LoggerFactory;

import java.io.FileOutputStream;
import java.io.FileWriter;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.util.*;
import java.util.stream.Collectors;

import static org.group_mmm.ArgParser.EquivType.*;

/**
 * <p>FalCAuN class.</p>
 *
 * @author Masaki Waga {@literal <masakiwaga@gmail.com>}
 */
@Slf4j
public class FalCAuN {
    private static int generationSize = 5;
    private static int childrenSize = 15 * 4;
    private static boolean resetWord = false;

    private static void printEquivSetting(ArgParser argParser, List<STLCost> stl) {
        final HashMap<ArgParser.EquivType, String> equivName = new HashMap<>();
        equivName.put(SA, "Simulated Annealing");
        equivName.put(RANDOM, "Random Test");
        equivName.put(HC, "Hill Climbing");
        equivName.put(GA, "Genetic Algorithm");

        System.out.println(equivName.get(argParser.getEquiv()) + " is used");

        System.out.println("STL size: " + stl.size());
        System.out.println("Length: " + argParser.getLength());
        System.out.println("maxTest: " + argParser.getMaxTest());

        switch (argParser.getEquiv()) {
            case SA:
                System.out.println("alpha:" + argParser.getAlpha());
            case HC:
                System.out.println("Generation size: " + generationSize);
                System.out.println("Children size:" + childrenSize);
                System.out.println("Reset word: " + resetWord);
                break;
            case GA:
                System.out.println("Population size: " + argParser.getPopulationSize());
                System.out.println("Crossover probability:" + argParser.getCrossoverProb());
                System.out.println("Mutation probability: " + argParser.getMutationProb());
                System.out.println("Selection kind: " + argParser.getSelectionKind());
                break;
            case WP:
                System.out.println("Maximum depth:" + argParser.getMaxDepth());
                break;
        }
    }

    /**
     * <p>main.</p>
     *
     * @param args an array of {@link java.lang.String} objects.
     * @throws java.lang.Exception if any.
     */
    public static void main(String[] args) throws Exception {
        ArgParser argParser = new ArgParser(args);
        if (argParser.isQuit()) {
            return;
        }

        if (!argParser.isVerbose()) {
            Logger MainLogger = (Logger) log;
            MainLogger.setLevel(Level.INFO);
            Logger LTSminVersionLogger = (Logger) LoggerFactory.getLogger(LTSminVersion.class);
            LTSminVersionLogger.setLevel(Level.INFO);
            Logger AbstractLTSminLogger = (Logger) LoggerFactory.getLogger(AbstractLTSmin.class);
            AbstractLTSminLogger.setLevel(Level.INFO);
            Logger EQSearchProblemLogger = (Logger) LoggerFactory.getLogger(EQSearchProblem.class);
            EQSearchProblemLogger.setLevel(Level.INFO);
            Logger GAEQOracleLogger = (Logger) LoggerFactory.getLogger(GAEQOracle.class);
            GAEQOracleLogger.setLevel(Level.INFO);
            Logger SimulinkSteadyStateGeneticAlgorithmLogger = (Logger) LoggerFactory.getLogger(EQSteadyStateGeneticAlgorithm.class);
            SimulinkSteadyStateGeneticAlgorithmLogger.setLevel(Level.INFO);
        }

        // Parse Simulink mapper
        List<Map<Character, Double>> inputMapper = InputMapperReader.parse(argParser.getInputMapperFile());
        OutputMapperReader outputMapperReader = new OutputMapperReader(argParser.getOutputMapperFile());
        outputMapperReader.parse();
        List<Character> largest = outputMapperReader.getLargest();
        List<Map<Character, Double>> outputMapper = outputMapperReader.getOutputMapper();
        log.debug("InputMapper: " + inputMapper);
        log.debug("OutputMapper: " + outputMapper);
        log.debug("Largest: " + largest);

        NumericSULMapper sulMapper = new NumericSULMapper(inputMapper, largest, outputMapper, argParser.getSigMap());

        // Parse STL formulas
        List<STLCost> stl;
        if (argParser.getStlFormula() != null) {
            stl = Collections.singletonList(STLCost.parseSTL(argParser.getStlFormula(), inputMapper, outputMapper, largest));
        } else if (argParser.getStlFile() != null) {
            stl = Files.lines(FileSystems.getDefault().getPath(argParser.getStlFile())).map(line ->
                    STLCost.parseSTL(line, inputMapper, outputMapper, largest)).collect(Collectors.toList());
        } else {
            throw new MissingOptionException("STL formula is not given");
        }
        List<String> ltlString = new ArrayList<>(stl.size());
        for (STLCost fml : stl) {
            ltlString.add(fml.toAbstractString());
        }
        if (argParser.isVerbose()) {
            log.debug("STL formulas: " + stl);
            log.debug("LTL formulas: " + ltlString);
        }
        int maxLTLLength = ltlString.stream().map(String::length).max(Integer::compareTo).orElse(0);
        if (maxLTLLength >= 8194) {
            log.warn("Size of the longest LTL string is " + maxLTLLength + ". This is probably too long.");
        }

        AdaptiveSTLUpdater adaptiveSTLUpdater;
        if (argParser.isAdaptiveSTL()) {
            log.info("adaptive STL updater is enabled");
            adaptiveSTLUpdater = new AdaptiveSTLList(stl, argParser.getLength());
        } else {
            log.info("adaptive STL updater is disabled");
            adaptiveSTLUpdater = new StaticSTLList(stl);
        }

        SimulinkSULVerifier verifier = new SimulinkSULVerifier(
                argParser.getInitScript(),
                argParser.getParamNames(),
                argParser.getStepTime(),
                argParser.getSimulinkSimulationStep(),
                adaptiveSTLUpdater,
                sulMapper);

        if (Objects.nonNull(argParser.getTimeout())) {
            if (argParser.isVerbose()) {
                log.debug("Timeout is set: " + argParser.getTimeout() + " seconds.");
            }
            verifier.setTimeout(argParser.getTimeout());
        } else {
            if (argParser.isVerbose()) {
                log.debug("Timeout is not set");
            }
        }
        switch (argParser.getEquiv()) {
            case HC:
                verifier.addHillClimbingEQOracleAll(argParser.getLength(), new Random(), argParser.getMaxTest(), generationSize, childrenSize, resetWord);
                break;
            case WP:
                verifier.addWpMethodEQOracle(argParser.getMaxDepth());
                break;
            case RANDOM:
                verifier.addRandomWordEQOracle(argParser.getLength(), argParser.getLength(), argParser.getMaxTest(), new Random(), 1);
                break;
            case SA:
                verifier.addSAEQOracleAll(argParser.getLength(), new Random(), argParser.getMaxTest(), generationSize, childrenSize, resetWord, argParser.getAlpha());
                break;
            case GA:
                verifier.addGAEQOracleAll(argParser.getLength(), argParser.getMaxTest(), argParser.getSelectionKind(), argParser.getPopulationSize(), argParser.getCrossoverProb(), argParser.getMutationProb());
                break;
            case PURE_RANDOM:
                SimulinkRandomTester tester = new SimulinkRandomTester(
                        argParser.getInitScript(),
                        argParser.getParamNames(),
                        argParser.getLength(),
                        argParser.getStepTime(),
                        ltlString,
                        stl,
                        sulMapper);
                if (Objects.nonNull(argParser.getTimeout())) {
                    if (argParser.isVerbose()) {
                        log.debug("Timeout is set: " + argParser.getTimeout() + " seconds.");
                    }
                    tester.setTimeout(argParser.getTimeout());
                } else {
                    if (argParser.isVerbose()) {
                        log.debug("Timeout is not set");
                    }
                }
                log.info("Pure random started");
                long startTime = System.nanoTime();
                boolean result = tester.run();
                long endTime = System.nanoTime();
                log.info("Pure random finished");
                log.info("Pure random Elapsed Time: " + ((endTime - startTime) / 1000000000.0) + " [sec]");
                if (result) {
                    log.info("All the given properties are verified");
                } else {
                    log.info("The following properties are falsified");
                    for (int i = 0; i < tester.getCexInput().size(); i++) {
                        if (tester.getCexInput().get(i) != null) {
                            printResult(i, tester.getCexProperty(), tester.getCexConcreteInput(), tester.getCexInput(), tester.getCexOutput());
                        }
                    }
                }
                return;
        }
        if (argParser.isVerbose()) {
            printEquivSetting(argParser, stl);
        }

        log.info("BBC started");
        TimeMeasure totalTime = new TimeMeasure();
        totalTime.start();
        boolean result = verifier.run();
        totalTime.stop();
        log.info("BBC finished");
        log.info("BBC Elapsed Time: " + totalTime.getSecond() + " [sec]");
        log.info("Simulink Execution: " + verifier.getSimulinkCount() + " times");
        log.info("Simulink Execution Time: " + verifier.getSimulationTimeSecond() + " [sec]");
        log.info("Simulink Execution for Equivalence Testing: " + verifier.getSimulinkCountForEqTest() + " times");

        if (result) {
            log.info("All the given properties are verified");
        } else {
            log.info("The following properties are falsified");
            for (int i = 0; i < verifier.getCexAbstractInput().size(); i++) {
                if (Objects.nonNull(verifier.getCexAbstractInput().get(i))) {
                    printResult(i, verifier.getCexProperty(), verifier.getCexConcreteInput(), verifier.getCexAbstractInput(), verifier.getCexOutput());
                }
            }
            log.info("Step time: " + argParser.getStepTime());
        }

        if (argParser.getDotFile() != null) {
            FileWriter writer = new FileWriter(argParser.getDotFile());
            verifier.writeDOTLearnedMealy(writer);
            writer.close();
        }

        if (argParser.getEtfFile() != null) {
            FileOutputStream outputStream = new FileOutputStream(argParser.getEtfFile());
            verifier.writeETFLearnedMealy(outputStream);
            outputStream.close();
        }
    }

    private static void printResult(int i, List<STLCost> cexProperties, List<Signal> cexConcreteInput, List<Word<String>> cexAbstractInput, List<Word<String>> cexOutput) {
        log.info("Property STL: {}", cexProperties.get(i).toString());
        log.info("Property LTL: {}", cexProperties.get(i).toLTLString());
        log.info("Concrete Input: {}", cexConcreteInput.get(i));
        log.info("Abstract Input: {}", cexAbstractInput.get(i));
        log.info("Output: {}", cexOutput.get(i));
    }
}
