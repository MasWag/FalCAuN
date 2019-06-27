package org.group_mmm;

import de.learnlib.api.oracle.PropertyOracle;
import org.apache.commons.cli.MissingOptionException;

import java.io.File;
import java.io.FileWriter;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;

public class Main {
    private static int generationSize = 5;
    private static int childrenSize = 15 * 4;
    private static boolean resetWord = false;
    private static List<Function<List<Double>, Double>> sigMap = Collections.emptyList();

    public static void main(String[] args) throws Exception {
        ArgParser argParser = new ArgParser(args);
        if (argParser.isQuit()) {
            return;
        }

        // Parse Simulink mapper
        List<Map<Character, Double>> inputMapper = InputMapperReader.parse(argParser.getInputMapperFile());
        OutputMapperReader outputMapperReader = new OutputMapperReader(argParser.getOutputMapperFile());
        outputMapperReader.parse();
        List<Character> largest = outputMapperReader.getLargest();
        List<Map<Character, Double>> outputMapper = outputMapperReader.getOutputMapper();
        if (argParser.isVerbose()) {
            System.out.println("InputMapper: " + inputMapper);
            System.out.println("OutputMapper: " + outputMapper);
            System.out.println("Largest: " + largest);
        }
        SimulinkSULMapper sulMapper = new SimulinkSULMapper(inputMapper, largest, outputMapper, sigMap);

        // Parse STL formulas
        List<STLCost> stl;
        if (argParser.getStlFormula() != null) {
            stl = Collections.singletonList(STLCost.parseSTL(argParser.getStlFormula(), outputMapper, largest));
        } else if (argParser.getStlFile() != null) {
            stl = Files.lines(FileSystems.getDefault().getPath(argParser.getStlFile())).map(line ->
                    STLCost.parseSTL(line, outputMapper, largest)).collect(Collectors.toList());
        } else {
            throw new MissingOptionException("STL formula is not given");
        }
        List<String> ltlString = new ArrayList<>(stl.size());
        for (STLCost fml : stl) {
            ltlString.add(fml.toAbstractString());
        }
        if (argParser.isVerbose()) {
            System.out.println("STL formulas: " + stl);
            System.out.println("LTL formulas: " + ltlString);
        }

        SimulinkVerifier verifier = new SimulinkVerifier(
                argParser.getInitScript(),
                argParser.getParamNames(),
                argParser.getStepTime(),
                ltlString,
                sulMapper);

/*
            if (useHillClimbing) {
                exampleAT.getVerifier().addHillClimbingEQOracle(costFunc,
                        15,
                        new Random(),
                        50000, 5, 15 * 4, resetWord,
                        exampleAT.getVerifier().getLtlFormulas().get(0));
            } else if (useGA) {
                exampleAT.getVerifier().addGAEQOracle(costFunc,
                        15,
                        new Random(),
                        10000, 3, 3, 2, 0.01, 0.8, resetWord);
            } else {
                exampleAT.getVerifier().addRandomWordEQOracle(15, 15, 100, new Random(), 1);
            }
*/
        switch (argParser.getEquiv()) {
            case HC:
                for (int i = 0; i < stl.size(); i++) {
                    PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle = verifier.getLtlFormulas().get(i);
                    verifier.addHillClimbingEQOracle(stl.get(i), argParser.getLength(), new Random(), argParser.getMaxTest(), generationSize, childrenSize, resetWord, ltlOracle);
                }
                if (argParser.isVerbose()) {
                    System.out.println("Hill Climing is used");
                    System.out.println("STL size: " + stl.size());
                    System.out.println("Length: " + argParser.getLength());
                    System.out.println("maxTest: " + argParser.getMaxTest());
                    System.out.println("Generation size: " + generationSize);
                    System.out.println("Children size:" + childrenSize);
                    System.out.println("Reset word: " + resetWord);
                }
                break;
            case WP:
                // verifier.addWpMethodEQOracle(30);
                throw new UnsupportedOperationException("Wp is not implemented yet!!");
            case RANDOM:
                verifier.addRandomWordEQOracle(argParser.getLength(), argParser.getLength(), argParser.getMaxTest(), new Random(), 1);
                if (argParser.isVerbose()) {
                    System.out.println("Random Test is used");
                    System.out.println("STL size: " + stl.size());
                    System.out.println("Min length: " + argParser.getLength());
                    System.out.println("Max length: " + argParser.getLength());
                    System.out.println("maxTest: " + argParser.getMaxTest());
                }
            case SA:
                for (int i = 0; i < stl.size(); i++) {
                    PropertyOracle.MealyPropertyOracle<String, String, String> ltlOracle = verifier.getLtlFormulas().get(i);
                    verifier.addSAEQOracle(stl.get(i), argParser.getLength(), new Random(), argParser.getMaxTest(), generationSize, childrenSize, resetWord, argParser.getAlpha(), ltlOracle);
                }
                if (argParser.isVerbose()) {
                    System.out.println("Simulated Annealing is used");
                    System.out.println("STL size: " + stl.size());
                    System.out.println("Length: " + argParser.getLength());
                    System.out.println("maxTest: " + argParser.getMaxTest());
                    System.out.println("Generation size: " + generationSize);
                    System.out.println("Children size:" + childrenSize);
                    System.out.println("Reset word: " + resetWord);
                    System.out.println("alpha:" + argParser.getAlpha());
                }
        }

        System.out.println("BBC started");
        long startTime = System.nanoTime();
        boolean result = verifier.run();
        long endTime = System.nanoTime();
        System.out.println("BBC finished");
        System.out.println("BBC Elapsed Time: " + ((endTime - startTime) / 1000000000.0) + " [sec]");
        if (result) {
            System.out.println("All the given properties are verified");
        } else {
            System.out.println("The following properties are falsified");
            for (int i = 0; i < verifier.getCexAbstractInput().size(); i++) {
                if (verifier.getCexAbstractInput().get(i) != null) {
                    System.out.println("Property STL: " + stl.get(i));
                    System.out.println("Property LTL: " + verifier.getCexProperty().get(i));
                    System.out.println("Concrete Input: " + verifier.getCexConcreteInput().get(i));
                    System.out.println("Abstract Input: " + verifier.getCexAbstractInput().get(i));
                    System.out.println("Output: " + verifier.getCexOutput().get(i));
                }
            }
        }

        if (argParser.getDotFile() != null) {
            FileWriter writer = new FileWriter(new File(argParser.getDotFile()));
            verifier.writeDOTLearnedMealy(writer);
            writer.close();
        }
    }
}
