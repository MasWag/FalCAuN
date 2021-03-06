package org.group_mmm;

import de.learnlib.api.oracle.MembershipOracle;
import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import org.assertj.core.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Disabled;

import java.io.File;
import java.io.FileWriter;
import java.lang.reflect.Field;
import java.util.*;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.*;

class AutotransExampleTest {
    static void executeRun(AutotransExample exampleAT, Function<Word<List<Double>>, Double> costFunc, boolean useHillClimbing, boolean useSA, boolean resetWord, String dotName) throws Exception {
        exampleAT.constructVerifier();

        if (useHillClimbing) {
            executeRun(exampleAT, costFunc, Kind.HC, resetWord, dotName);
        } else if (useSA) {
            executeRun(exampleAT, costFunc, Kind.SA, resetWord, dotName);
        } else {
            executeRun(exampleAT, costFunc, Kind.RANDOM, resetWord, dotName);
        }
    }

    static void executeRun(AutotransExample exampleAT, Function<Word<List<Double>>, Double> costFunc, Kind kind, boolean resetWord, String dotName) throws Exception {
        exampleAT.constructVerifier();

        switch (kind) {
            case HC:
                exampleAT.getVerifier().addHillClimbingEQOracle(costFunc,
                        15,
                        new Random(),
                        50000, 5, 15 * 4, resetWord,
                        exampleAT.getVerifier().getLtlFormulas().get(0));
                break;
            case SA:
                exampleAT.getVerifier().addSAEQOracle(costFunc,
                        15,
                        new Random(),
                        50000, 5, 15 * 4, resetWord, 0.3,
                        exampleAT.getVerifier().getLtlFormulas().get(0));
                break;
            case RANDOM:
                exampleAT.getVerifier().addRandomWordEQOracle(15, 15, 100, new Random(), 1);
                break;
            case GA:
                exampleAT.getVerifier().addGAEQOracle(costFunc,
                        30,
                        500000, ArgParser.GASelectionKind.BestSolution, 30,// Generation size must be odd number
                        0.8, 0.01,
                        exampleAT.getVerifier().getLtlFormulas().get(0));
                break;
        }

        assertFalse(exampleAT.getVerifier().run());

        FileWriter writer = new FileWriter(new File(dotName));
        exampleAT.getVerifier().writeDOTLearnedMealy(writer);
        writer.close();

        System.out.println("CexInput: " + exampleAT.getVerifier().getCexAbstractInput());
        System.out.println("CexOutput: " + exampleAT.getVerifier().getCexOutput());
    }

    enum Kind {
        RANDOM,
        SA,
        HC,
        GA
    }

    @Test
    @Disabled
    void constructAT1() {
        AutotransExample exampleAT = new AutotransExample(10.0);
        System.out.println(exampleAT.constructAT1(4200));
    }

    @Test
    @Disabled
    void memOracleBB() throws Exception {
        AutotransExample exampleAT = new AutotransExample(10.0);
        exampleAT.setProperties(Collections.singletonList(
                exampleAT.constructAT1(4500.0)));
        exampleAT.constructVerifier();

        // Get BlackBoxVerifier
        Field field = exampleAT.getVerifier().getClass().getDeclaredField("verifier");
        field.setAccessible(true);
        BlackBoxVerifier verifier = (BlackBoxVerifier) field.get(exampleAT.getVerifier());

        // Get MemOracle
        field = verifier.getClass().getDeclaredField("memOracle");
        field.setAccessible(true);
        @SuppressWarnings("unchecked")
        MembershipOracle.MealyMembershipOracle<String, String> memOracle =
                (MembershipOracle.MealyMembershipOracle<String, String>) field.get(verifier);

        WordBuilder<String> input = new WordBuilder<>();
        input.append("bb");
        WordBuilder<String> expected = new WordBuilder<>();
        expected.append("ba2");
        assertEquals(expected.toWord(), memOracle.answerQuery(input.toWord()));
    }

    /**
     * AT1 in [HAF14] for omega = 4500
     */
    @Test
    @Disabled
    void runAT1() throws Exception {
        AutotransExample exampleAT1 = new AutotransExample(10.0);
        exampleAT1.setProperties(new ArrayList<>(
                Collections.singletonList(
                        exampleAT1.constructAT1(4500.0))));

        exampleAT1.constructVerifier();

        assertFalse(exampleAT1.getVerifier().run());
        System.out.println("CexInput: " + exampleAT1.getVerifier().getCexAbstractInput());
        System.out.println("CexOutput: " + exampleAT1.getVerifier().getCexOutput());
    }

    /**
     * AT2 in [HAF14] for v = 120 and omega = 4500
     */
    @Test
    @Disabled
    void runAT2() throws Exception {
        AutotransExample exampleAT2 = new AutotransExample(10.0);
        exampleAT2.setProperties(new ArrayList<>(
                Collections.singletonList(
                        exampleAT2.constructAT2(120, 4500.0))));
        exampleAT2.constructVerifier();

        assertFalse(exampleAT2.getVerifier().run());
        System.out.println("CexInput: " + exampleAT2.getVerifier().getCexAbstractInput());
        System.out.println("CexOutput: " + exampleAT2.getVerifier().getCexOutput());
    }

    /**
     * AT2 in [HAF14] for v = 160 and omega = 5000
     */
    @Test
    @Disabled
    void runAT2_1() throws Exception {
        AutotransExample exampleAT2 = new AutotransExample(10.0);
        List<Map<Character, Double>> outputMapper = exampleAT2.getOutputMapper();

        // Construct the input mapper
        {
            Map<Character, Double> throttleMapper = new HashMap<>();
            throttleMapper.put('a', 0.0);
            //throttleMapper.put('b', 20.0);
            //throttleMapper.put('c', 40.0);
            //throttleMapper.put('d', 60.0);
            //throttleMapper.put('e', 80.0);
            throttleMapper.put('f', 100.0);

            Map<Character, Double> brakeMapper = new HashMap<>();
            brakeMapper.put('a', 0.0);
            //brakeMapper.put('b', 50.0);
            //brakeMapper.put('c', 100.0);
            //brakeMapper.put('d', 150.0);
            //brakeMapper.put('e', 200.0);
            //brakeMapper.put('f', 250.0);
            //brakeMapper.put('g', 300.0);
            brakeMapper.put('h', 325.0);

            exampleAT2.setInputMapper(new ArrayList<>(Arrays.asList(throttleMapper, brakeMapper)));
        }

        //{120, 160, 170, 200}.
        Map<Character, Double> velocityMapper = new HashMap<>();
        velocityMapper.put('a', 80.0);
        velocityMapper.put('b', 120.0);
        velocityMapper.put('c', 160.0);
        //velocityMapper.put('d', 70.0);
        velocityMapper.put('e', 170.0);
        //velocityMapper.put('f', 110.0);
        velocityMapper.put('g', 180.0);
        outputMapper.set(0, velocityMapper);


        //{4500, 5000, 5200, 5500}.
        Map<Character, Double> rotationMapper = new HashMap<>();
        rotationMapper.put('a', 4000.0);
        rotationMapper.put('b', 4500.0);
        rotationMapper.put('c', 4750.0);
        rotationMapper.put('d', 5000.0);
        //rotationMapper.put('e', 5000.0);
        //rotationMapper.put('f', 5200.0);
        //rotationMapper.put('g', 5500.0);
        //rotationMapper.put('h', 5750.0);
        //rotationMapper.put('i', 6000.0);
        outputMapper.set(1, rotationMapper);

        exampleAT2.setOutputMapper(outputMapper);
        exampleAT2.setProperties(new ArrayList<>(
                Collections.singletonList(
                        exampleAT2.constructAT2(160, 5000.0))));

        exampleAT2.constructVerifier();

        // exampleAT2.getVerifier().addRandomWalkEQOracle(0.3, 100, new Random());
        // exampleAT2.getVerifier().addBFOracle(100.0);
        exampleAT2.getVerifier().addRandomWordEQOracle(5, 30, 100, new Random(), 1);
        // exampleAT2.getVerifier().addCompleteExplorationEQOracle(1, 10, 1);

        // We cannot falsify this example
        assertTrue(exampleAT2.getVerifier().run());
        //System.out.println(exampleAT2.getVerifier().run());

        exampleAT2.getVerifier().visualizeLearnedMealy();
    }

    @Test
    @Disabled
    void constructAT3() {
        AutotransExample exampleAT = new AutotransExample(10.0);

        //{120, 160, 170, 200}.
        Map<Character, Double> velocityMapper = new HashMap<>();
        velocityMapper.put('a', 80.0);


        //{4500, 5000, 5200, 5500}.
        Map<Character, Double> rotationMapper = new HashMap<>();
        rotationMapper.put('a', 4000.0);

        Map<Character, Double> gearMapper = new HashMap<>();
        gearMapper.put('1', 1.0);
        gearMapper.put('2', 2.0);
        gearMapper.put('3', 3.0);

        exampleAT.setOutputMapper(new ArrayList<>(
                Arrays.asList(velocityMapper, rotationMapper, gearMapper)));

        ArrayList<Character> largest = new ArrayList<>(Arrays.asList('b', 'b', '4'));
        exampleAT.setLargest(largest);


        String gear1 = "((output == \"aa1\") || (output == \"ab1\") || (output == \"ba1\") || (output == \"bb1\"))";
        String gear2 = "((output == \"aa2\") || (output == \"ab2\") || (output == \"ba2\") || (output == \"bb2\"))";

        String expected = "[] (( " + gear2 + " && X " + gear1 + " ) -> (" + "X(!" + gear2 + ") && " + "X(X(!" + gear2 + ")) " + "))";

        assertEquals(expected, exampleAT.constructAT3());
    }

    @Test
    @Disabled
    void runAT3() throws Exception {
        AutotransExample exampleAT = new AutotransExample(1.0);

        //{120, 160, 170, 200}.
        Map<Character, Double> velocityMapper = new HashMap<>();
        velocityMapper.put('a', 100.0);


        //{4500, 5000, 5200, 5500}.
        Map<Character, Double> rotationMapper = new HashMap<>();
        rotationMapper.put('a', 4000.0);

        Map<Character, Double> gearMapper = new HashMap<>();
        gearMapper.put('1', 1.0);
        gearMapper.put('2', 2.0);
        gearMapper.put('3', 3.0);

        exampleAT.setOutputMapper(new ArrayList<>(
                Arrays.asList(velocityMapper, rotationMapper, gearMapper)));

        ArrayList<Character> largest = new ArrayList<>(Arrays.asList('b', 'b', '4'));
        exampleAT.setLargest(largest);

        exampleAT.setProperties(new ArrayList<>(
                Collections.singletonList(
                        exampleAT.constructAT3())));

        exampleAT.constructVerifier();
        exampleAT.getVerifier().addRandomWordEQOracle(5, 30, 100, new Random(), 1);
        System.out.println(exampleAT.getVerifier().run());

        exampleAT.getVerifier().visualizeLearnedMealy();

        System.out.println("CexInput: " + exampleAT.getVerifier().getCexAbstractInput());
        System.out.println("CexOutput: " + exampleAT.getVerifier().getCexOutput());
    }

    /**
     * The tests for ATs in HAF14
     */
    @Nested
    class HAF14_AT {
        private AutotransExample exampleAT;

        @BeforeEach
        void setUp() {
            exampleAT = new AutotransExample(2.0);

            // Construct the input mapper
            {
                Map<Character, Double> throttleMapper = new HashMap<>();
                throttleMapper.put('a', 0.0);
                //throttleMapper.put('b', 20.0);
                //throttleMapper.put('c', 40.0);
                //throttleMapper.put('d', 60.0);
                //throttleMapper.put('e', 80.0);
                throttleMapper.put('f', 100.0);

                Map<Character, Double> brakeMapper = new HashMap<>();
                brakeMapper.put('a', 0.0);
                //brakeMapper.put('b', 50.0);
                //brakeMapper.put('c', 100.0);
                //brakeMapper.put('d', 150.0);
                //brakeMapper.put('e', 200.0);
                //brakeMapper.put('f', 250.0);
                //brakeMapper.put('g', 300.0);
                brakeMapper.put('h', 325.0);

                exampleAT.setInputMapper(new ArrayList<>(Arrays.asList(throttleMapper, brakeMapper)));
            }
        }

        @Test
        @Disabled
        void runAT1() throws Exception {
            Map<Character, Double> velocityMapper = new HashMap<>();

            Map<Character, Double> rotationMapper = new HashMap<>();
            rotationMapper.put('a', 4000.0);
            rotationMapper.put('b', 4500.0);


            Map<Character, Double> gearMapper = new HashMap<>();

            exampleAT.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));

            ArrayList<Character> largest = new ArrayList<>(Arrays.asList('c', 'X', 'X'));
            exampleAT.setLargest(largest);

            STLAtomic atomic = new STLAtomic(1, STLAtomic.Operation.lt, 4500.0);

            atomic.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));
            atomic.setLargest(largest);

            STLCost costFunc = new STLGlobal(atomic);

            exampleAT.setProperties(new ArrayList<>(Collections.singletonList(costFunc.toAbstractString())));

            boolean useHillClimbing = true;
            boolean useGA = false;
            boolean resetWord = false;

            executeRun(exampleAT, costFunc, useHillClimbing, useGA, resetWord, "./runAT1Learned.dot");
        }
    }

    /**
     * The tests for ATs in ZESAH18
     */
    @Nested
    class ZESAH18_AT {
        private AutotransExample exampleAT;

        @BeforeEach
        void setUp() {
            exampleAT = new AutotransExample(1.0);

            // Construct the input mapper
            {
                Map<Character, Double> throttleMapper = new HashMap<>();
                throttleMapper.put('a', 0.0);
                //throttleMapper.put('b', 20.0);
                //throttleMapper.put('c', 40.0);
                //throttleMapper.put('d', 60.0);
                //throttleMapper.put('e', 80.0);
                throttleMapper.put('f', 100.0);

                Map<Character, Double> brakeMapper = new HashMap<>();
                brakeMapper.put('a', 0.0);
                //brakeMapper.put('b', 50.0);
                //brakeMapper.put('c', 100.0);
                //brakeMapper.put('d', 150.0);
                //brakeMapper.put('e', 200.0);
                //brakeMapper.put('f', 250.0);
                //brakeMapper.put('g', 300.0);
                brakeMapper.put('h', 325.0);

                exampleAT.setInputMapper(new ArrayList<>(Arrays.asList(throttleMapper, brakeMapper)));
            }
        }

        @Test
        @Disabled
        void runS1() throws Exception {
            //{120, 160, 170, 200}.
            Map<Character, Double> velocityMapper = new HashMap<>();
            velocityMapper.put('a', 80.0);
            velocityMapper.put('b', 100.0);
            velocityMapper.put('c', 120.0);


            //{4500, 5000, 5200, 5500}.
            Map<Character, Double> rotationMapper = new HashMap<>();

            Map<Character, Double> gearMapper = new HashMap<>();

            exampleAT.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));

            ArrayList<Character> largest = new ArrayList<>(Arrays.asList('d', 'X', 'X'));
            exampleAT.setLargest(largest);

            exampleAT.setProperties(new ArrayList<>(
                    Collections.singletonList(
                            exampleAT.constructS1(120))));

            exampleAT.constructVerifier();
            exampleAT.getVerifier().addRandomWordEQOracle(20, 30, 100, new Random(), 1);
            // exampleAT.getVerifier().addRandomWordEQOracle(20, 30, 100, new Random(), 1);
            // exampleAT.getVerifier().addWpMethodEQOracle(30);
            //exampleAT.getVerifier().addRandomWalkEQOracle(0.1, 100, new Random());
            assertFalse(exampleAT.getVerifier().run());

            FileWriter writer = new FileWriter(new File("./runS1Learned.dot"));
            exampleAT.getVerifier().writeDOTLearnedMealy(writer);
            writer.close();

            System.out.println("CexInput: " + exampleAT.getVerifier().getCexAbstractInput());
            System.out.println("CexOutput: " + exampleAT.getVerifier().getCexOutput());
        }

        @Test
        @Disabled
        void setTimeout() throws Exception {
            Map<Character, Double> velocityMapper = new HashMap<>();
            velocityMapper.put('a', 80.0);
            velocityMapper.put('b', 100.0);
            velocityMapper.put('c', 120.0);

            Map<Character, Double> rotationMapper = new HashMap<>();

            Map<Character, Double> gearMapper = new HashMap<>();

            exampleAT.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));

            ArrayList<Character> largest = new ArrayList<>(Arrays.asList('d', 'X', 'X'));
            exampleAT.setLargest(largest);

            exampleAT.setProperties(new ArrayList<>(
                    Collections.singletonList(
                            exampleAT.constructS1(120))));

            exampleAT.constructVerifier();
            long timeout = 1000;
            exampleAT.getVerifier().setTimeout(timeout);

            exampleAT.getVerifier().addRandomWordEQOracle(20, 30, 100, new Random(), 1);
            exampleAT.getVerifier().addRandomWordEQOracle(1, 2, 1, new Random(), 1);

            long startTime = System.nanoTime();
            assertTrue(exampleAT.getVerifier().run());
            long endTime = System.nanoTime();
            Assertions.assertThat(endTime - startTime).isGreaterThan(timeout * 1000000000);
        }

        @Disabled
        @Test
        void easyS1() throws Exception {
            Map<Character, Double> velocityMapper = new HashMap<>();
            velocityMapper.put('a', 40.0);
            velocityMapper.put('c', 120.0);

            Map<Character, Double> rotationMapper = new HashMap<>();

            Map<Character, Double> gearMapper = new HashMap<>();

            exampleAT.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));

            ArrayList<Character> largest = new ArrayList<>(Arrays.asList('d', 'X', 'X'));
            exampleAT.setLargest(largest);

            exampleAT.setProperties(new ArrayList<>(
                    Collections.singletonList(
                            exampleAT.constructS1(40))));

            exampleAT.constructVerifier();
            long timeout = 1000;
            exampleAT.getVerifier().setTimeout(timeout);

            exampleAT.getVerifier().addRandomWordEQOracle(20, 30, 100000, new Random(), 1);

            long startTime = System.nanoTime();
            assertFalse(exampleAT.getVerifier().run());
            long endTime = System.nanoTime();
            Assertions.assertThat(endTime - startTime).isLessThan(timeout * 1000000000);
        }

        @Disabled
        @Test
        void constructS1() {
            Map<Character, Double> velocityMapper = new HashMap<>();
            velocityMapper.put('a', 80.0);
            velocityMapper.put('b', 100.0);
            velocityMapper.put('c', 120.0);

            Map<Character, Double> rotationMapper = new HashMap<>();

            Map<Character, Double> gearMapper = new HashMap<>();

            exampleAT.setOutputMapper(Arrays.asList(velocityMapper, rotationMapper, gearMapper));

            List<Character> largest = new ArrayList<>(Arrays.asList('d', 'X', 'X'));
            exampleAT.setLargest(largest);

            String expected = "[]((output==\"aXX\")||(output==\"cXX\")||(output==\"bXX\"))";
            STLAtomic atomic = new STLAtomic(0, STLAtomic.Operation.lt, 120.0);
            atomic.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));
            atomic.setLargest(largest);
            STLCost costFunc = new STLGlobal(atomic);

            String costFormula = costFunc.toAbstractString().replaceAll(" ", "");

            assertEquals(expected, costFormula);
        }

        @Test
        @Disabled
        void runS1Func(Kind kind) throws Exception {
            //{120, 160, 170, 200}.
            Map<Character, Double> velocityMapper = new HashMap<>();
            velocityMapper.put('a', 80.0);
            velocityMapper.put('b', 100.0);
            velocityMapper.put('c', 120.0);


            //{4500, 5000, 5200, 5500}.
            Map<Character, Double> rotationMapper = new HashMap<>();

            Map<Character, Double> gearMapper = new HashMap<>();

            exampleAT.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));

            List<Character> largest = new ArrayList<>(Arrays.asList('d', 'X', 'X'));
            exampleAT.setLargest(largest);

            exampleAT.setProperties(Collections.singletonList(
                    exampleAT.constructS1(120)));

            boolean resetWord = false;

            Function<Word<List<Double>>, Double> costFunc = new STLGlobal(new STLAtomic(0, STLAtomic.Operation.lt, 120.0));

            executeRun(exampleAT, costFunc, kind, resetWord, "./runS1Learned.dot");
        }

        @Test
        @Disabled
        void runS1SA() throws Exception {
            runS1Func(Kind.SA);
        }

        @Test
        @Disabled
        void runS1GA() throws Exception {
            runS1Func(Kind.GA);
        }


        @Test
        @Disabled
        void runS2() throws Exception {
            //{120, 160, 170, 200}.
            Map<Character, Double> velocityMapper = new HashMap<>();
            velocityMapper.put('a', 10.0);
            velocityMapper.put('b', 20.0);

            //{4500, 5000, 5200, 5500}.
            Map<Character, Double> rotationMapper = new HashMap<>();

            Map<Character, Double> gearMapper = new HashMap<>();
            gearMapper.put('1', 1.0);
            gearMapper.put('2', 2.0);
            gearMapper.put('3', 3.0);


            exampleAT.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));

            List<Character> largest = new ArrayList<>(Arrays.asList('c', 'X', '4'));
            exampleAT.setLargest(largest);

            exampleAT.setProperties(new ArrayList<>(
                    Collections.singletonList(
                            exampleAT.constructS2(20))));

            boolean useHillClimbing = true;
            boolean useGA = false;
            boolean resetWord = false;

            Function<Word<List<Double>>, Double> costFunc =
                    new STLGlobal(new STLImply(new STLAtomic(2, STLAtomic.Operation.eq, 3),
                            new STLAtomic(0, STLAtomic.Operation.gt, 20)));

            executeRun(exampleAT, costFunc, useHillClimbing, useGA, resetWord, "./runS2Learned.dot");
        }

        @Test
        @Disabled
        void runS1andS2() throws Exception {
            Map<Character, Double> velocityMapper = new HashMap<>();
            //velocityMapper.put('a', 10.0);
            velocityMapper.put('b', 20.0);
            //velocityMapper.put('c', 80.0);
            //velocityMapper.put('d', 100.0);
            velocityMapper.put('e', 120.0);

            Map<Character, Double> rotationMapper = new HashMap<>();

            Map<Character, Double> gearMapper = new HashMap<>();
            // gearMapper.put('1', 1.0);
            gearMapper.put('2', 2.0);
            gearMapper.put('3', 3.0);


            exampleAT.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));

            List<Character> largest = new ArrayList<>(Arrays.asList('f', 'X', '4'));
            exampleAT.setLargest(largest);

            exampleAT.setProperties(new ArrayList<>(Arrays.asList(
                    exampleAT.constructS1(120),
                    exampleAT.constructS2(20))));

            exampleAT.constructVerifier();
            boolean useHillClimbing = true;
            boolean useGA = false;
            boolean resetWord = false;

            Function<Word<List<Double>>, Double> costFuncS1 = new STLGlobal(new STLAtomic(0, STLAtomic.Operation.lt, 120.0));

            Function<Word<List<Double>>, Double> costFuncS2 =
                    new STLGlobal(new STLImply(new STLAtomic(2, STLAtomic.Operation.eq, 3),
                            new STLAtomic(0, STLAtomic.Operation.gt, 20)));

            if (useHillClimbing) {
                exampleAT.getVerifier().addHillClimbingEQOracle(costFuncS1,
                        15,
                        new Random(),
                        50000, 5, 15 * 4, resetWord, exampleAT.getVerifier().getLtlFormulas().get(0));
                exampleAT.getVerifier().addHillClimbingEQOracle(costFuncS2,
                        15,
                        new Random(),
                        50000, 5, 15 * 4, resetWord, exampleAT.getVerifier().getLtlFormulas().get(1));
            } else if (useGA) {
                exampleAT.getVerifier().addGAEQOracle(costFuncS1,
                        15,
                        10000, ArgParser.GASelectionKind.BestSolution, 3, 15.0, 0.6, exampleAT.getVerifier().getLtlFormulas().get(0));
            } else {
                exampleAT.getVerifier().addRandomWordEQOracle(15, 15, 100, new Random(), 1);
            }

            assertFalse(exampleAT.getVerifier().run());

            FileWriter writer = new FileWriter(new File("./runS1-S2Learned.dot"));
            exampleAT.getVerifier().writeDOTLearnedMealy(writer);
            writer.close();

            System.out.println("CexInput: " + exampleAT.getVerifier().getCexAbstractInput());
            System.out.println("CexOutput: " + exampleAT.getVerifier().getCexOutput());
        }

        void runS4Func(Kind kind) throws Exception {
            Map<Character, Double> velocityMapper = new HashMap<>();
            //velocityMapper.put('a', 50.0);
            velocityMapper.put('b', 65.0);
            //velocityMapper.put('c', 80.0);
            velocityMapper.put('d', 100.0);
            velocityMapper.put('e', 120.0);

            //{4500, 5000, 5200, 5500}.
            Map<Character, Double> rotationMapper = new HashMap<>();

            Map<Character, Double> gearMapper = new HashMap<>();


            exampleAT.setOutputMapper(Arrays.asList(velocityMapper, rotationMapper, gearMapper));

            List<Character> largest = new ArrayList<>(Arrays.asList('f', 'X', 'X'));
            exampleAT.setLargest(largest);

            exampleAT.setProperties(new ArrayList<>(
                    Collections.singletonList(
                            exampleAT.constructS4(100.0, 65.0))));

            boolean resetWord = false;

            STLCost costFunc =
                    new STLOr(new STLSub(new STLGlobal(new STLAtomic(0, STLAtomic.Operation.lt, 100)), 0, 13),
                            new STLSub(new STLGlobal(new STLAtomic(0, STLAtomic.Operation.gt, 65.0)), 14, 14));

            executeRun(exampleAT, costFunc, kind, resetWord, "./runS4Learned.dot");
        }

        @Test
        @Disabled
        void runS4SA() throws Exception {
            runS4Func(Kind.SA);
        }

        @Test
        @Disabled
        void runS4GA() throws Exception {
            runS4Func(Kind.GA);
        }

        @Test
        @Disabled
        void runS5() throws Exception {
            Map<Character, Double> velocityMapper = new HashMap<>();

            Map<Character, Double> rotationMapper = new HashMap<>();
            rotationMapper.put('a', 600.0);
            rotationMapper.put('b', 2000.0);
            rotationMapper.put('c', 3000.0);
            rotationMapper.put('d', 4000.0);
            rotationMapper.put('e', 4770.0);

            Map<Character, Double> gearMapper = new HashMap<>();


            exampleAT.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));

            List<Character> largest = new ArrayList<>(Arrays.asList('X', 'f', 'X'));
            exampleAT.setLargest(largest);

            exampleAT.setProperties(new ArrayList<>(
                    Collections.singletonList(
                            exampleAT.constructS5(4770.0, 600.0))));

            boolean useHillClimbing = false;
            boolean useSA = true;
            boolean resetWord = false;

            STLCost costFunc = new STLGlobal(
                    new STLOr(
                            new STLAtomic(1, STLAtomic.Operation.lt, 4770),
                            new STLNext(new STLAtomic(1, STLAtomic.Operation.gt, 600.0), true)
                    ));

            executeRun(exampleAT, costFunc, useHillClimbing, useSA, resetWord, "./runS5Learned.dot");
        }

        @Test
        @Disabled
        void runS4andS5() throws Exception {
            Map<Character, Double> velocityMapper = new HashMap<>();
            //velocityMapper.put('a', 50.0);
            velocityMapper.put('b', 65.0);
            //velocityMapper.put('c', 80.0);
            velocityMapper.put('d', 100.0);
            //velocityMapper.put('e', 120.0);

            //{4500, 5000, 5200, 5500}.
            Map<Character, Double> rotationMapper = new HashMap<>();
            rotationMapper.put('a', 600.0);
            //rotationMapper.put('b', 2000.0);
            //rotationMapper.put('c', 3000.0);
            //rotationMapper.put('d', 4000.0);
            rotationMapper.put('e', 4770.0);

            Map<Character, Double> gearMapper = new HashMap<>();


            exampleAT.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));

            List<Character> largest = new ArrayList<>(Arrays.asList('f', 'f', 'X'));
            exampleAT.setLargest(largest);

            exampleAT.setProperties(new ArrayList<>(
                    Arrays.asList(
                            exampleAT.constructS4(100.0, 65.0),
                            exampleAT.constructS5(4770.0, 600.0))));

            List<STLCost> costFuncList = Arrays.asList(
                    new STLOr(new STLSub(new STLGlobal(new STLAtomic(0, STLAtomic.Operation.lt, 100)), 0, 13),
                            new STLSub(new STLGlobal(new STLAtomic(0, STLAtomic.Operation.gt, 65.0)), 14, 14)),
                    new STLGlobal(
                            new STLOr(
                                    new STLAtomic(1, STLAtomic.Operation.lt, 4770),
                                    new STLNext(new STLAtomic(1, STLAtomic.Operation.gt, 600.0), true))));


            exampleAT.constructVerifier();

            for (int i = 0; i < costFuncList.size(); i++) {
                exampleAT.getVerifier().addHillClimbingEQOracle(costFuncList.get(i),
                        15,
                        new Random(),
                        50000, 5, 15 * 4, false,
                        exampleAT.getVerifier().getLtlFormulas().get(i));
            }


            assertFalse(exampleAT.getVerifier().run());

            FileWriter writer = new FileWriter(new File("./runS4andS5Learned.dot"));
            exampleAT.getVerifier().writeDOTLearnedMealy(writer);
            writer.close();

            System.out.println("CexInput: " + exampleAT.getVerifier().getCexAbstractInput());
            System.out.println("CexOutput: " + exampleAT.getVerifier().getCexOutput());
        }

    }

    /**
     * The original tests for ATs
     */
    @Nested
    class Original {
        private AutotransExample exampleAT;

        @BeforeEach
        void setUp() {
            exampleAT = new AutotransExample(2.0);

            // Construct the input mapper
            {
                Map<Character, Double> throttleMapper = new HashMap<>();
                throttleMapper.put('a', 0.0);
                //throttleMapper.put('b', 20.0);
                //throttleMapper.put('c', 40.0);
                //throttleMapper.put('d', 60.0);
                //throttleMapper.put('e', 80.0);
                throttleMapper.put('f', 100.0);

                Map<Character, Double> brakeMapper = new HashMap<>();
                brakeMapper.put('a', 0.0);
                //brakeMapper.put('b', 50.0);
                //brakeMapper.put('c', 100.0);
                //brakeMapper.put('d', 150.0);
                //brakeMapper.put('e', 200.0);
                //brakeMapper.put('f', 250.0);
                //brakeMapper.put('g', 300.0);
                brakeMapper.put('h', 325.0);

                exampleAT.setInputMapper(new ArrayList<>(Arrays.asList(throttleMapper, brakeMapper)));
            }
        }

        @Test
        @Disabled
        void runM1Func(Kind kind) throws Exception {
            //{120, 160, 170, 200}.
            Map<Character, Double> velocityMapper = new HashMap<>();
            velocityMapper.put('a', 30.0);
            velocityMapper.put('b', 90.0);


            //{4500, 5000, 5200, 5500}.
            Map<Character, Double> rotationMapper = new HashMap<>();

            Map<Character, Double> gearMapper = new HashMap<>();

            exampleAT.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));

            List<Character> largest = new ArrayList<>(Arrays.asList('c', 'X', 'X'));
            exampleAT.setLargest(largest);

            STLAtomic highVelocity = new STLAtomic(0, STLAtomic.Operation.lt, 90.0);
            STLAtomic lowVelocity = new STLAtomic(0, STLAtomic.Operation.gt, 30.0);

            highVelocity.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));
            highVelocity.setLargest(largest);

            lowVelocity.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));
            lowVelocity.setLargest(largest);

            STLCost costFunc = new STLOr(Arrays.asList(
                    new STLSub(new STLGlobal(lowVelocity), 0, 2),
                    new STLSub(new STLGlobal(highVelocity), 3, 5),
                    new STLSub(new STLGlobal(lowVelocity), 6, 8),
                    new STLSub(new STLGlobal(highVelocity), 9, 11),
                    new STLSub(new STLGlobal(lowVelocity), 12, 14)));

            exampleAT.setProperties(new ArrayList<>(
                    Collections.singletonList(costFunc.toAbstractString())));

            boolean resetWord = false;

            executeRun(exampleAT, costFunc, kind, resetWord, "./runM1Learned.dot");
        }

        @Test
        @Disabled
        void runM1SA() throws Exception {
            runM1Func(Kind.SA);
        }

        @Test
        @Disabled
        void runM1GA() throws Exception {
            runM1Func(Kind.GA);
        }

        @Test
        @Disabled
        void runM2() throws Exception {
            // Construct the input mapper
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
                //brakeMapper.put('c', 100.0);
                brakeMapper.put('d', 150.0);
                //brakeMapper.put('e', 200.0);
                //brakeMapper.put('f', 250.0);
                //brakeMapper.put('g', 300.0);
                brakeMapper.put('h', 325.0);

                exampleAT.setInputMapper(new ArrayList<>(Arrays.asList(throttleMapper, brakeMapper)));
            }

            //{120, 160, 170, 200}.
            Map<Character, Double> velocityMapper = new HashMap<>();
            velocityMapper.put('a', 30.0);
            velocityMapper.put('b', 60.0);
            velocityMapper.put('c', 90.0);


            //{4500, 5000, 5200, 5500}.
            Map<Character, Double> rotationMapper = new HashMap<>();

            Map<Character, Double> gearMapper = new HashMap<>();

            exampleAT.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));

            List<Character> largest = new ArrayList<>(Arrays.asList('d', 'X', 'X'));
            exampleAT.setLargest(largest);

            STLAtomic highVelocity = new STLAtomic(0, STLAtomic.Operation.lt, 90.0);
            STLAtomic lowVelocity = new STLAtomic(0, STLAtomic.Operation.gt, 30.0);

            highVelocity.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));
            highVelocity.setLargest(largest);

            lowVelocity.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));
            lowVelocity.setLargest(largest);

            STLCost costFunc = new STLOr(Arrays.asList(
                    new STLSub(new STLGlobal(lowVelocity), 0, 4),
                    new STLSub(new STLGlobal(highVelocity), 5, 9),
                    new STLSub(new STLGlobal(lowVelocity), 10, 14)));

            exampleAT.setProperties(new ArrayList<>(
                    Collections.singletonList(costFunc.toAbstractString())));

            boolean useHillClimbing = true;
            boolean useGA = false;
            boolean resetWord = false;

            executeRun(exampleAT, costFunc, useHillClimbing, useGA, resetWord, "./runM2Learned.dot");
        }

        @Test
        @Disabled
        void runRevS4() throws Exception {
            Map<Character, Double> velocityMapper = new HashMap<>();
            velocityMapper.put('a', 50.0);
            velocityMapper.put('b', 65.0);
            velocityMapper.put('c', 80.0);
            velocityMapper.put('d', 100.0);
            velocityMapper.put('e', 120.0);

            //{4500, 5000, 5200, 5500}.
            Map<Character, Double> rotationMapper = new HashMap<>();

            Map<Character, Double> gearMapper = new HashMap<>();


            exampleAT.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));

            List<Character> largest = new ArrayList<>(Arrays.asList('f', 'X', 'X'));
            exampleAT.setLargest(largest);

            STLAtomic highVelocity = new STLAtomic(0, STLAtomic.Operation.lt, 100.0);
            STLAtomic lowVelocity = new STLAtomic(0, STLAtomic.Operation.gt, 65.0);

            highVelocity.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));
            highVelocity.setLargest(largest);

            lowVelocity.setOutputMapper(new ArrayList<>(
                    Arrays.asList(velocityMapper, rotationMapper, gearMapper)));
            lowVelocity.setLargest(largest);

            STLCost costFunc =
                    new STLOr(new STLSub(new STLGlobal(highVelocity), 1, 13),
                            new STLSub(new STLGlobal(lowVelocity), 14, 14));

            exampleAT.setProperties(Collections.singletonList(costFunc.toAbstractString()));

            boolean useHillClimbing = true;
            boolean useGA = false;
            boolean resetWord = false;

            executeRun(exampleAT, costFunc, useHillClimbing, useGA, resetWord, "./runRevS4Learned.dot");
        }
    }
}
