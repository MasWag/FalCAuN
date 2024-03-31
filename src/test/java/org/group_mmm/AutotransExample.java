package org.group_mmm;

import org.apache.commons.collections4.CollectionUtils;

import java.util.*;
import java.util.function.Function;

/**
 * Example of the Automatic transmission model in <a href="https://easychair.org/publications/open/4bfq">HAF14</a>
 * <p>
 * The AT model two inputs (throttle and brake) and three outputs (velocity, rotation, gear).
 */
public class AutotransExample {
    private final String PWD = System.getenv("PWD");
    private final String initScript = "cd " + PWD + "/src/test/resources/MATLAB; initAT;";
    private final List<String> paramNames = Arrays.asList("throttle", "brake");
    private final int velocityIndex = 0;
    private final int rotationIndex = 1;
    private final int gearIndex = 2;
    private List<List<Character>> abstractOutputs = new ArrayList<>();
    private List<List<Double>> concreteOutputs = new ArrayList<>();
    private double signalStep;
    private List<Map<Character, Double>> inputMapper;
    private List<Map<Character, Double>> outputMapper;
    private List<Character> largest;
    private NumericSULVerifier verifier;
    private AdaptiveSTLUpdater properties;
    private NumericSULMapper mapper;
    private List<Function<IOSignalPiece, Double>> sigMap = new ArrayList<>();

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
            //{120, 160, 170, 200}.
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
        mapper = new NumericSULMapper(inputMapper, largest, outputMapper, new SignalMapper(sigMap));
        setOutputMaps();
    }

    private void setOutputMaps() {
        abstractOutputs.clear();
        concreteOutputs.clear();
        for (Map<Character, Double> entry : outputMapper) {
            ArrayList<Character> cList = new ArrayList<>(entry.keySet());
            ArrayList<Double> dList = new ArrayList<>(entry.values());
            assert cList.size() == dList.size();
            abstractOutputs.add(cList);
            concreteOutputs.add(dList);
        }
    }

    public List<Map<Character, Double>> getInputMapper() {
        return inputMapper;
    }

    void setInputMapper(List<Map<Character, Double>> inputMapper) {
        this.inputMapper = inputMapper;
        mapper = new NumericSULMapper(inputMapper, largest, outputMapper, new SignalMapper(sigMap));
    }

    List<Map<Character, Double>> getOutputMapper() {
        return outputMapper;
    }

    void setOutputMapper(List<Map<Character, Double>> outputMapper) {
        this.outputMapper = outputMapper;
        mapper = new NumericSULMapper(inputMapper, largest, outputMapper, new SignalMapper(sigMap));
        setOutputMaps();
    }

    public List<Character> getLargest() {
        return largest;
    }

    void setLargest(List<Character> largest) {
        this.largest = largest;
        mapper = new NumericSULMapper(inputMapper, largest, outputMapper, new SignalMapper(sigMap));
        setOutputMaps();
    }

    public String getInitScript() {
        return initScript;
    }

    public List<String> getParamNames() {
        return paramNames;
    }

    public Double getSignalStep() {
        return signalStep;
    }

    NumericSULVerifier getVerifier() {
        return verifier;
    }

    public AdaptiveSTLUpdater getProperties() {
        return properties;
    }

    void setProperties(AdaptiveSTLUpdater properties) {
        this.properties = properties;
    }

    public NumericSULMapper getMapper() {
        return mapper;
    }

    public List<Function<IOSignalPiece, Double>> getSigMap() {
        return sigMap;
    }

    public void setSigMap(List<Function<IOSignalPiece, Double>> sigMap) {
        this.sigMap = sigMap;
        mapper = new NumericSULMapper(inputMapper, largest, outputMapper, new SignalMapper(this.sigMap));
    }

    private List<Character> constructSmallerAPs(int index, double threshold) {
        int bsResult = Collections.binarySearch(concreteOutputs.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? bsResult : (~bsResult - 1);
        ArrayList<Character> resultAPs = new ArrayList<>(abstractOutputs.get(index).subList(0, thresholdIndex + 1));
        if (bsResult < 0 && thresholdIndex == abstractOutputs.size() - 1) {
            resultAPs.add(largest.get(index));
        }

        return resultAPs;
    }

    private List<Character> constructLargerAPs(int index, double threshold) {
        int bsResult = Collections.binarySearch(concreteOutputs.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? bsResult : (~bsResult - 1);
        ArrayList<Character> resultAPs = new ArrayList<>(abstractOutputs.get(index).subList(thresholdIndex + 1, abstractOutputs.get(index).size()));

        resultAPs.add(largest.get(index));


        return resultAPs;
    }

    private ArrayList<Character> constructEqAPs(int index, double threshold) {
        int bsResult = Collections.binarySearch(concreteOutputs.get(index), threshold);
        int thresholdIndex = (bsResult >= 0) ? bsResult : (~bsResult);
        ArrayList<Character> resultAPs = new ArrayList<>();
        if (!abstractOutputs.get(index).isEmpty()) {
            resultAPs.addAll(abstractOutputs.get(index).subList(thresholdIndex, thresholdIndex + 1));
        }
        if (abstractOutputs.get(index).isEmpty() ||
                (bsResult < 0 && thresholdIndex == abstractOutputs.size() - 1)) {
            resultAPs.add(largest.get(index));
        }
        assert resultAPs.size() == 1;

        return resultAPs;
    }

    private List<Character> constructAllAPs(int index) {
        ArrayList<Character> resultAPs = new ArrayList<>(abstractOutputs.get(index));
        resultAPs.add(largest.get(index));
        return resultAPs;
    }

    private List<String> constructProductAPs(List<Character> velocityAPs,
                                             List<Character> rotationAPs,
                                             List<Character> gearAPs) {
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

        List<Character> velocityAPs = constructAllAPs(velocityIndex);
        List<Character> rotationAPs = constructSmallerAPs(rotationIndex, rotationThreshold);
        List<Character> gearAPs = constructAllAPs(gearIndex);

        List<String> APs = constructProductAPs(velocityAPs, rotationAPs, gearAPs);

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

        List<Character> velocityAPs = constructSmallerAPs(velocityIndex, velocityThreshold);
        List<Character> gearAPs = constructAllAPs(gearIndex);
        List<Character> rotationAPs = constructSmallerAPs(rotationIndex, rotationThreshold);

        List<String> APs = constructProductAPs(velocityAPs, rotationAPs, gearAPs);

        builder.append(String.join(" || ", APs));
        builder.append(")");
        return builder.toString();
    }

    /**
     * Construct the LTL formula for AT3 in HAF14
     *
     * @return The constructed LTL formula.
     */
    String constructAT3() {
        StringBuilder builder = new StringBuilder();
        builder.append("[] (");

        List<Character> velocityAPs = constructAllAPs(velocityIndex);
        List<Character> gear1APs = constructEqAPs(gearIndex, 1.0);
        List<Character> gear2APs = constructEqAPs(gearIndex, 2.0);
        List<Character> rotationAPs = constructAllAPs(rotationIndex);

        String gear1APString = String.join(" || ",
                constructProductAPs(velocityAPs, rotationAPs, gear1APs));
        String gear2APString = String.join(" || ",
                constructProductAPs(velocityAPs, rotationAPs, gear2APs));
        signalStep = 1.0;
        builder.append("( (");
        builder.append(gear2APString);
        builder.append(") && X (");
        builder.append(gear1APString);
        builder.append(") ) -> (");
        builder.append("X(!(");
        builder.append(gear2APString);
        builder.append(")) && ");
        builder.append("X(X(!(");
        builder.append(gear2APString);
        builder.append("))) " + ")");


        builder.append(")");
        return builder.toString();
    }

    /**
     * Construct the LTL formula for S1 in ZESAH18
     * <p>
     * This specification can be easily falsified by hill-climbing.
     *
     * @param velocityThreshold The threshold of the velocity. It is 120 in ZHSAH18.
     * @return The constructed LTL formula.
     */
    String constructS1(double velocityThreshold) {
        StringBuilder builder = new StringBuilder();
        builder.append("[] (");

        List<Character> velocityAPs = constructSmallerAPs(velocityIndex, velocityThreshold);
        List<Character> rotationAPs = constructAllAPs(rotationIndex);
        List<Character> gearAPs = constructAllAPs(gearIndex);

        List<String> APs = constructProductAPs(velocityAPs, rotationAPs, gearAPs);

        builder.append(String.join(" || ", APs));
        builder.append(")");
        return builder.toString();
    }

    /**
     * Construct the LTL formula for S2 in ZESAH18
     * <p>
     * This is difficult for robustness-guided falsification because of the information loss when gear != 3
     *
     * @param velocityThreshold The threshold of the velocity. It is 20 in ZHSAH18.
     * @return The constructed LTL formula.
     * <p>
     * We use (gear == 3 -> v >= 20) iff. (gear != 3 || v >= 20) to make the formula shorter.
     */
    String constructS2(double velocityThreshold) {
        StringBuilder builder = new StringBuilder();
        builder.append("[] (");

        List<Character> velocityAllAPs = constructAllAPs(velocityIndex);
        List<Character> velocityLargerAPs = constructLargerAPs(velocityIndex, velocityThreshold);
        List<Character> rotationAPs = constructAllAPs(rotationIndex);
        List<Character> gearAllAPs = constructAllAPs(gearIndex);
        List<Character> gear3APs = constructEqAPs(gearIndex, 3.0);

        List<String> allAPStrings = constructProductAPs(velocityAllAPs, rotationAPs, gearAllAPs);
        List<String> gear3APStrings = constructProductAPs(velocityAllAPs, rotationAPs, gear3APs);
        Collection<String> gearN3APStrings = CollectionUtils.subtract(allAPStrings, gear3APStrings);

        Set<String> APs = new HashSet<>(constructProductAPs(velocityLargerAPs, rotationAPs, gearAllAPs));
        APs.addAll(gearN3APStrings);


        builder.append(String.join(" || ", APs));
        builder.append(")");
        return builder.toString();
    }

    /**
     * Construct the LTL formula for S4 in ZESAH18
     * <p>
     * This is difficult for the falsification algorithm only using hill-climbing.
     *
     * @param ltThreshold This is 100.0 in ZHSAH18
     * @param gtThreshold This is 65.0 in ZHSAH18
     * @return The constructed LTL formula.
     */
    String constructS4(double ltThreshold, double gtThreshold) {
        StringBuilder builder = new StringBuilder();
        builder.append("(");

        final int numOfSamples = (int) Math.ceil(30.0 / signalStep);
        List<Character> velocity100APs = constructSmallerAPs(velocityIndex, ltThreshold);
        List<Character> velocity65APs = constructLargerAPs(velocityIndex, gtThreshold);

        List<Character> rotationAPs = constructAllAPs(rotationIndex);
        List<Character> gearAPs = constructAllAPs(gearIndex);
        String velocity100String = String.join(" || ",
                constructProductAPs(velocity100APs, rotationAPs, gearAPs));
        String velocity65String = String.join(" || ",
                constructProductAPs(velocity65APs, rotationAPs, gearAPs));
        List<String> builder100Array = new ArrayList<>();
        for (int i = 0; i < numOfSamples - 1; i++) {
            StringBuilder builder100 = new StringBuilder();
            for (int j = 0; j < i; j++) {
                builder100.append("(X");
            }

            builder100.append("(");
            builder100.append(velocity100String);
            builder100.append(")");

            for (int j = 0; j < i; j++) {
                builder100.append(")");
            }
            builder100Array.add(builder100.toString());
        }
        builder.append(String.join(" && ", builder100Array));
        builder.append(") || (");
        for (int i = 0; i < numOfSamples; i++) {
            builder.append("(X");
        }

        builder.append("(");
        builder.append(velocity65String);
        builder.append(")");

        for (int i = 0; i < numOfSamples; i++) {
            builder.append(")");
        }


        builder.append(")");
        return builder.toString();
    }

    /**
     * Construct the LTL formula for S5 in ZESAH18
     * <p>
     * This is difficult for the falsification algorithm only using hill-climbing.
     *
     * @param ltThreshold This is 4770 in ZHSAH18
     * @param gtThreshold This is 600 in ZHSAH18
     * @return The constructed LTL formula.
     */
    String constructS5(double ltThreshold, double gtThreshold) {
        StringBuilder builder = new StringBuilder();
        builder.append("[] (");

        List<Character> velocityAPs = constructAllAPs(velocityIndex);

        List<Character> rotation4770APs = constructSmallerAPs(rotationIndex, ltThreshold);
        List<Character> rotation600APs = constructLargerAPs(rotationIndex, gtThreshold);

        List<Character> gearAPs = constructAllAPs(gearIndex);

        String rotation4770Strings = String.join(" || ",
                constructProductAPs(velocityAPs, rotation4770APs, gearAPs));
        String rotation600Strings = String.join(" || ",
                constructProductAPs(velocityAPs, rotation600APs, gearAPs));
        List<String> builder100Array = new ArrayList<>();

        builder.append("(");
        builder.append(rotation4770Strings);
        builder.append(")");

        builder.append(" || ");


        builder.append("( X(");
        builder.append(rotation600Strings);
        builder.append("))");

        builder.append(")");
        return builder.toString();
    }

    void constructVerifier() throws Exception {
        verifier = new SimulinkSULVerifier(initScript, paramNames, signalStep, properties, mapper);
    }
}
