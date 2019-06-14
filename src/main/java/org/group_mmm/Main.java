package org.group_mmm;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Map;
import java.util.function.Function;

public class Main {

    private static ArrayList<Function<ArrayList<Double>, Double>> sigMap = new ArrayList<>(Collections.emptyList());
    private static SimulinkVerifier verifier;
    private static int maxTest = 50000;

    public static void main(String[] args) {
        ArgParser argParser = new ArgParser(args);
        if (argParser.isQuit()) {
            return;
        }

        // Parse input mapper
        try {
            ArrayList<Map<Character, Double>> inputMapper = InputMapperReader.parse(argParser.getInputMapperFile());
            OutputMapperReader outputMapperReader = new OutputMapperReader(argParser.getOutputMapperFile());
            ArrayList<Character> largest = outputMapperReader.getLargest();
            ArrayList<Map<Character, Double>> outputMapper = outputMapperReader.getOutputMapper();
            SimulinkSULMapper sulMapper = new SimulinkSULMapper(inputMapper, largest, outputMapper, sigMap);
/*
            verifier = new SimulinkVerifier(initScript, paramNames, argParser.getStepTime(), properties, sulMapper);


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

            switch (argParser.getEquiv()) {
                case HC:
                    verifier.addHillClimbingEQOracle(costFunc, argParser.getLength(), new Random(), maxTest);
                    break;
                case WP:
                    break;
                case RANDOM:
                    break;
            }*/

        } catch (IOException ignore) {

        }

        System.out.println("Hello World!!");
    }
}
