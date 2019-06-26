package org.group_mmm.examples;

import org.group_mmm.STLCost;
import org.group_mmm.SimulinkSULMapper;
import org.group_mmm.SimulinkVerifier;

import java.io.FileOutputStream;
import java.util.*;

/**
 * Generates ETF file of AT_S1
 */
public class ATS1ETF {
    public static void main(String[] args) throws Exception {
        /// Configure the output
        final String etfFileName = "/tmp/ATS1.etf";
        FileOutputStream stream = new FileOutputStream(etfFileName);

        /// Configure Simulink
        String initScript = "cd ./src/resources/MATLAB/; initAT";
        final List<String> paramName = Arrays.asList("throttle", "brake");
        final double signalStep = 2.0;

        Map<Character, Double> throttleMapper = new HashMap<>();
        throttleMapper.put('a', 0.0);
        throttleMapper.put('f', 100.0);

        Map<Character, Double> brakeMapper = new HashMap<>();
        brakeMapper.put('a', 0.0);
        brakeMapper.put('h', 325.0);

        List<Map<Character, Double>> inputMapper = new ArrayList<>(Arrays.asList(throttleMapper, brakeMapper));

        //{120, 160, 170, 200}.
        Map<Character, Double> velocityMapper = new HashMap<>();
        velocityMapper.put('a', 80.0);
        velocityMapper.put('b', 100.0);
        velocityMapper.put('c', 120.0);


        //{4500, 5000, 5200, 5500}.
        Map<Character, Double> rotationMapper = new HashMap<>();

        Map<Character, Double> gearMapper = new HashMap<>();

        List<Map<Character, Double>> outputMapper = Arrays.asList(velocityMapper, rotationMapper, gearMapper);

        List<Character> largest = new ArrayList<>(Arrays.asList('d', 'X', 'X'));

        SimulinkSULMapper mapper = new SimulinkSULMapper(inputMapper, largest, outputMapper, Collections.emptyList());

        STLCost costFunc = STLCost.parseSTL("alw(signal(0) < 120.0)", outputMapper, largest);
        final List<String> properties = Collections.singletonList(costFunc.toAbstractString());

        SimulinkVerifier verifier = new SimulinkVerifier(initScript, paramName, signalStep, properties, mapper);

        verifier.addHillClimbingEQOracle(costFunc,
                15,
                new Random(),
                500,
                5,
                15 * 4,
                false,
                verifier.getLtlFormulas().get(0));

        verifier.run();
        verifier.writeETFLearnedMealy(stream);
    }
}