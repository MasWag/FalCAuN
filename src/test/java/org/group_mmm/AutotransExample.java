package org.group_mmm;

import java.util.*;
import java.util.function.Function;

/**
 * Example of the Automatic transmission model in HAF14 (https://easychair.org/publications/open/4bfq)
 * <p>
 * The AT model two inputs (throttle and brake) and three outputs (velocity, rotation, gear).
 */
public class AutotransExample {
    private final String initScript = "cd ./src/test/resources/MATLAB; initAT;";
    private final ArrayList<String> paramNames = new ArrayList<>(Arrays.asList("throttle", "brake"));
    private final double signalStep;
    private ArrayList<Map<Character, Double>> inputMapper;
    private ArrayList<Map<Character, Double>> outputMapper;
    private ArrayList<Character> largest;
    private SimulinkVerifier verifier;
    private ArrayList<String> properties;
    private SimulinkSULMapper mapper;
    private ArrayList<Function<ArrayList<Double>, Double>> sigMap = new ArrayList<>();
    ArrayList<ArrayList<Character>> abstractOutputs = new ArrayList<>();
    ArrayList<ArrayList<Double>> concreteOutputs = new ArrayList<>();
    private final int velocityIndex = 0;
    private final int rotationIndex = 1;
    private final int gearIndex = 2;

    private void setOutputMaps() {
        for (Map<Character, Double> entry : outputMapper) {
            ArrayList<Character> cList = new ArrayList<>(entry.keySet());
            ArrayList<Double> dList = new ArrayList<>(entry.values());
            assert cList.size() == dList.size();
            abstractOutputs.add(cList);
            concreteOutputs.add(dList);
        }
    }

    AutotransExample(double signalStep) {
        this.signalStep = signalStep;

        // Construct the default mapper
        {
            Map<Character, Double> throttleMapper = new HashMap<>();
            throttleMapper.put('a', 0.0);
            //throttleMapper.put('b', 20.0);
            throttleMapper.put('c', 40.0);
            //throttleMapper.put('d', 60.0);
            //throttleMapper.put('e', 80.0);
            throttleMapper.put('f', 100.0);

            Map<Character, Double> brakeMapper = new HashMap<>();
            brakeMapper.put('a', 0.0);
            //brakeMapper.put('b', 50.0);
            brakeMapper.put('c', 100.0);
            //brakeMapper.put('d', 150.0);
            brakeMapper.put('e', 200.0);
            //brakeMapper.put('f', 250.0);
            //brakeMapper.put('g', 300.0);
            brakeMapper.put('h', 325.0);

            inputMapper = new ArrayList<>(Arrays.asList(throttleMapper, brakeMapper));
        }
        {
            Map<Character, Double> velocityMapper = new HashMap<>();
            velocityMapper.put('a', 10.0);
            //velocityMapper.put('b', 30.0);
            velocityMapper.put('c', 50.0);
            //velocityMapper.put('d', 70.0);
            velocityMapper.put('e', 90.0);
            //velocityMapper.put('f', 110.0);
            velocityMapper.put('g', 130.0);

            //{4500, 5000, 5200, 5500}.
            Map<Character, Double> rotationMapper = new HashMap<>();
            //rotationMapper.put('a', 4000.0);
            rotationMapper.put('b', 4250.0);
            rotationMapper.put('c', 4500.0);
            rotationMapper.put('d', 4750.0);
            //rotationMapper.put('e', 5000.0);
            rotationMapper.put('f', 5200.0);
            //rotationMapper.put('g', 5500.0);
            //rotationMapper.put('h', 5750.0);
            //rotationMapper.put('i', 6000.0);

            Map<Character, Double> gearMapper = new HashMap<>();
            //gearMapper.put('1', 1.0);
            //gearMapper.put('2', 2.0);
            //gearMapper.put('3', 3.0);


            outputMapper = new ArrayList<>(Arrays.asList(velocityMapper, rotationMapper, gearMapper));
            largest = new ArrayList<>(Arrays.asList('X', 'X', 'X'));
        }
        mapper = new SimulinkSULMapper(inputMapper, largest, outputMapper, sigMap);
        setOutputMaps();
    }

    public String getInitScript() {
        return initScript;
    }

    public ArrayList<String> getParamNames() {
        return paramNames;
    }

    public Double getSignalStep() {
        return signalStep;
    }

    public SimulinkVerifier getVerifier() {
        return verifier;
    }

    public ArrayList<String> getProperties() {
        return properties;
    }

    void setProperties(ArrayList<String> properties) {
        this.properties = properties;
    }

    public SimulinkSULMapper getMapper() {
        return mapper;
    }

    public ArrayList<Function<ArrayList<Double>, Double>> getSigMap() {
        return sigMap;
    }

    private ArrayList<Character> constructSmallerAPs(int index, double threshold) {
        int bsResult = Collections.binarySearch(concreteOutputs.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? bsResult : (~bsResult - 1);
        ArrayList<Character> resultAPs = new ArrayList<>(abstractOutputs.get(index).subList(0, thresholdIndex + 1));
        if (bsResult < 0 && thresholdIndex == abstractOutputs.size() - 1) {
            resultAPs.add(largest.get(index));
        }

        return resultAPs;
    }

    private ArrayList<Character> constructAllAPs(int index) {
        ArrayList<Character> resultAPs = new ArrayList<>(abstractOutputs.get(index));
        resultAPs.add(largest.get(index));
        return resultAPs;
    }

    private ArrayList<String> constructProductAPs(ArrayList<Character> velocityAPs,
                                                  ArrayList<Character> rotationAPs,
                                                  ArrayList<Character> gearAPs) {
        ArrayList<String> APs = new ArrayList<>();
        for (Character velocityAP : velocityAPs) {
            for (Character rotationAP : rotationAPs) {
                for (Character gearAP : gearAPs) {
                    APs.add("(output == \"" + velocityAP + rotationAP + gearAP + "\")");
                }
            }
        }
        return APs;
    }

    /**
     * Construct the LTL formula for AT1 in HAF14
     *
     * @param rotationThreshold The threshold of the engine rotation. The recommended values are {4500, 5000, 5200, 5500}.
     * @return The constructed LTL formula.
     */
    String constructAT1(double rotationThreshold) {
        StringBuilder builder = new StringBuilder();
        builder.append("[] (");

        ArrayList<Character> velocityAPs = constructAllAPs(velocityIndex);
        ArrayList<Character> rotationAPs = constructSmallerAPs(rotationIndex, rotationThreshold);
        ArrayList<Character> gearAPs = constructAllAPs(gearIndex);

        ArrayList<String> APs = constructProductAPs(velocityAPs, rotationAPs, gearAPs);

        builder.append(String.join(" || ", APs));
        builder.append(")");
        return builder.toString();
    }

    /**
     * Construct the LTL formula for AT2 in HAF14
     *
     * @param velocityThreshold The threshold of the velocity (mph). The recommended values are {120, 160, 170, 200}.
     * @param rotationThreshold The threshold of the engine rotation (RPM). The recommended values are {4500, 5000, 5200, 5500}.
     * @return The constructed LTL formula.
     */
    String constructAT2(double velocityThreshold, double rotationThreshold) {
        StringBuilder builder = new StringBuilder();
        builder.append("[] (");

        ArrayList<Character> velocityAPs = constructSmallerAPs(velocityIndex, velocityThreshold);
        ArrayList<Character> gearAPs = constructAllAPs(gearIndex);
        ArrayList<Character> rotationAPs = constructSmallerAPs(rotationIndex, rotationThreshold);

        ArrayList<String> APs = constructProductAPs(velocityAPs, rotationAPs, gearAPs);

        builder.append(String.join(" || ", APs));
        builder.append(")");
        return builder.toString();
    }

    void constructVerifier() throws Exception {
        verifier = new SimulinkVerifier(initScript, paramNames, signalStep, properties, mapper);
    }
}
