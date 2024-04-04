package net.maswag;

import net.automatalib.word.Word;
import net.automatalib.word.WordBuilder;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.util.*;

import static java.lang.Double.*;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import net.maswag.TemporalLogic.STLCost;
import net.maswag.TemporalSub.STLSub;
import net.maswag.TemporalOr.STLOr;
import net.maswag.TemporalGlobally.STLGlobally;
import net.maswag.TemporalImply.STLImply;
import net.maswag.TemporalEventually.STLEventually;


class STLCostTest {
    private List<String> concreteExpected;
    private List<String> abstractExpected;
    private List<STLCost> formulas;

    @BeforeEach
    void setUp() {
        concreteExpected = Arrays.asList(
                "[] ( output(0) < 120.000000 )",
                "[] ( ( output(2) == 3.000000 ) -> ( output(0) > 20.000000 ) )"
        );
        abstractExpected = Arrays.asList(
                "[] ( ( output == \"aaa\" ) || ( output == \"aac\" ) || ( output == \"bab\" ) || ( output == \"aab\" ) || ( output == \"baa\" ) || ( output == \"bac\" ) )",
                "[] ( ( output == \"aaa\" ) || ( output == \"aac\" ) || ( output == \"caa\" ) || ( output == \"bab\" ) || ( output == \"baa\" ) || ( output == \"cac\" ) || ( output == \"bac\" ) || ( output == \"cab\" ) )"
        ); // || ( output == "aab" )
        Map<Character, Double> velocityMap = new HashMap<>();
        Map<Character, Double> rotationMap = new HashMap<>();
        Map<Character, Double> gearMap = new HashMap<>();
        velocityMap.put('a', 20.0);
        velocityMap.put('b', 120.0);
        gearMap.put('a', 2.0);
        gearMap.put('b', 3.0);
        List<Map<Character, Double>> outputMapper = Arrays.asList(velocityMap, rotationMap, gearMap);
        List<Character> largest = Arrays.asList('c', 'a', 'c');
        List<STLOutputAtomic> atomics = new ArrayList<>();
        atomics.add(new STLOutputAtomic(0, STLOutputAtomic.Operation.lt, 120.0));
        atomics.add(new STLOutputAtomic(2, STLOutputAtomic.Operation.eq, 3));
        atomics.add(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 20));
        for (STLOutputAtomic atomic : atomics) {
            atomic.setAtomic(outputMapper, largest);
        }

        formulas = Arrays.asList(
                new STLGlobally(atomics.get(0)),
                new STLGlobally(new STLImply(atomics.get(1), atomics.get(2)))
        );

        assert concreteExpected.size() == formulas.size();
    }

    @Test
    void toStringTest() {
        for (int i = 0; i < concreteExpected.size(); i++) {
            assertEquals(concreteExpected.get(i), formulas.get(i).toString());
        }
    }

    @Test
    void toAbstractStringTest() {
        for (int i = 0; i < abstractExpected.size(); i++) {
            assertEquals(abstractExpected.get(i), formulas.get(i).toAbstractString());
        }
    }

    @Test
    void equalityTest() {
        STLFactory factory = new STLFactory();
        List<STLCost> formulas = new ArrayList<>();
        formulas.add(factory.parse("[] ( output(0) < 120.000000 )"));
        formulas.add(factory.parse("[] ( output(0) < 120.000000 )"));
        // STL Formulas are considered the same if they have the same string representation
        assertEquals(formulas.get(0), formulas.get(1));
    }

    @Nested
    class Bug201906171356Test {
        IOSignal input;

        @BeforeEach
        void setUp() {
            WordBuilder<List<Double>> builder = new WordBuilder<>();
            builder.append(new ArrayList<>(Arrays.asList(31.659005778016194, 3735.3257077648086, 1.0)));
            builder.append(new ArrayList<>(Arrays.asList(49.710367875876926, 3605.836356859281, 2.0)));
            builder.append(new ArrayList<>(Arrays.asList(49.26918040521577, 603.7208189546687, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(59.808271898139644, 4188.159777396062, 2.0)));
            builder.append(new ArrayList<>(Arrays.asList(73.93237187014977, 3687.184003724488, 3.0)));
            builder.append(new ArrayList<>(Arrays.asList(80.53789904775707, 3938.7191807934432, 3.0)));
            builder.append(new ArrayList<>(Arrays.asList(75.1999337450591, 603.7214000782157, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(84.06382802684683, 4079.673264283264, 3.0)));
            builder.append(new ArrayList<>(Arrays.asList(78.60903068946162, 600.0, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(72.94452732917028, 603.7213779955085, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(82.02192575448733, 3997.384539137563, 3.0)));
            builder.append(new ArrayList<>(Arrays.asList(80.39777620517314, 603.7214425522945, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(82.83787200700355, 3062.240095871121, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(85.75230478701785, 3117.4431309247016, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(88.39317330844652, 3165.812526140048, 4.0)));
            input = new IOSignal(builder.toWord(), builder.toWord());
            assert input.size() == 15;
        }

        @Test
        void ATExampleS4() {
            STLCost costFunc =
                    new STLOr(new STLSub(new STLGlobally(new STLOutputAtomic(0, STLOutputAtomic.Operation.lt, 100)), 0, 13),
                            new STLSub(new STLGlobally(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 65.0)), 14, 14));
            assertNotEquals(POSITIVE_INFINITY, costFunc.apply(input));
        }

        @Test
        void ATExampleS4AndTextRepl() {
            STLFactory factory = new STLFactory();
            STLCost costFuncExt =
                    new STLOr(new STLSub(new STLGlobally(new STLOutputAtomic(0, STLOutputAtomic.Operation.lt, 100)), 0, 13),
                            new STLSub(new STLGlobally(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 65.0)), 14, 14));
            STLCost costFunc = factory.parse("([]_[0,13] (signal(0) < 100)) || ([]_[14,14] (signal(0) > 65.0))");
            assertEquals(costFuncExt.apply(input), costFunc.apply(input));
        }
    }

    @Nested
    class Bug20200427Test {
        IOSignal input;

        @BeforeEach
        void setUp() {
            WordBuilder<List<Double>> builder = new WordBuilder<>();
            builder.append(new ArrayList<>(Arrays.asList(31.659005778016194, 3735.3257077648086, 1.0)));
            builder.append(new ArrayList<>(Arrays.asList(49.710367875876926, 3605.836356859281, 2.0)));
            builder.append(new ArrayList<>(Arrays.asList(49.26918040521577, 603.7208189546687, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(59.808271898139644, 4188.159777396062, 2.0)));
            builder.append(new ArrayList<>(Arrays.asList(73.93237187014977, 3687.184003724488, 3.0)));
            builder.append(new ArrayList<>(Arrays.asList(80.53789904775707, 3938.7191807934432, 3.0)));
            builder.append(new ArrayList<>(Arrays.asList(75.1999337450591, 603.7214000782157, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(84.06382802684683, 4079.673264283264, 3.0)));
            builder.append(new ArrayList<>(Arrays.asList(78.60903068946162, 600.0, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(72.94452732917028, 603.7213779955085, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(82.02192575448733, 3997.384539137563, 3.0)));
            builder.append(new ArrayList<>(Arrays.asList(80.39777620517314, 603.7214425522945, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(82.83787200700355, 3062.240095871121, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(85.75230478701785, 3117.4431309247016, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(88.39317330844652, 3165.812526140048, 4.0)));
            builder.append(new ArrayList<>(Arrays.asList(88.39317330844652, 3165.812526140048, 4.0)));
            input = new IOSignal(builder.toWord(), builder.toWord());
            assert input.size() == 16;
        }

        @Test
        void AT6() {
            STLCost costFunc1Atomic =
                    new STLOutputAtomic(1, STLOutputAtomic.Operation.lt, 3000);
            TemporalOp<List<Double>> costFunc1Global =
                    new STLGlobally(costFunc1Atomic);
            STLCost costFunc1 =
                    new STLSub(costFunc1Global, 0, 15);
            STLCost costFunc2 =
                    new STLSub(new STLGlobally(new STLOutputAtomic(0, STLOutputAtomic.Operation.lt, 35.0)), 0, 2);
            STLCost costFunc = new STLImply(costFunc1, costFunc2);

            RoSI robustness1Atomic = costFunc1Atomic.getRoSI(input);
            assertNotEquals(POSITIVE_INFINITY, robustness1Atomic.lowerBound);
            assertNotEquals(NEGATIVE_INFINITY, robustness1Atomic.lowerBound);

            RoSI robustness1Global = costFunc1Global.getRoSIRaw(input);
            assertEquals(-1188.159777396062, robustness1Global.lowerBound.doubleValue());
            assertEquals(-1188.159777396062, robustness1Global.upperBound.doubleValue());

            RoSI robustness1 = costFunc1.getRoSI(input);
            assertNotEquals(POSITIVE_INFINITY, robustness1.lowerBound);
            assertNotEquals(NEGATIVE_INFINITY, robustness1.lowerBound);

            RoSI robustness2 = costFunc2.getRoSI(input);
            assertNotEquals(POSITIVE_INFINITY, robustness2.upperBound);
            assertNotEquals(NEGATIVE_INFINITY, robustness2.upperBound);

            double robustness = costFunc.apply(input);

            assertEquals(max(-robustness1.lowerBound, robustness2.upperBound), robustness);
        }

        @Test
        void AT6TextRepl() {
            STLFactory factory = new STLFactory();
            STLCost costFuncExt =
                    new STLImply(new STLSub(new STLGlobally(new STLOutputAtomic(1, STLOutputAtomic.Operation.lt, 3000)), 0, 15),
                            new STLSub(new STLGlobally(new STLOutputAtomic(0, STLOutputAtomic.Operation.lt, 35.0)), 0, 2));
            STLCost costFunc = factory.parse("((alw_[0, 15] (signal(1) < 3000.0)) -> (alw_[0, 2] (signal(0) < 35.0)))");
            assertEquals(costFuncExt.apply(input), costFunc.apply(input));
        }
    }

    @Nested
    class Bug20210308Test {
        IOSignal<List<Double>> input;

        @BeforeEach
        void setUp() {
            WordBuilder<List<Double>> builder = new WordBuilder<>();
            builder.append(new ArrayList<>(Arrays.asList(0.0, 10.0, 20.0, 30.0, 40.0)));
            builder.append(new ArrayList<>(Arrays.asList(0.0, 10.0, 20.0, 30.0, 40.0)));
            builder.append(new ArrayList<>(Arrays.asList(-50.000000000001535, -13.37570312500029, 13.247187500000098, 29.868671875, 40.0)));
            builder.append(new ArrayList<>(Arrays.asList(-59.99954600070697, -47.81534062500114, -36.600771875001236, -25.25632812500158, 12.988749999999484)));
            builder.append(new ArrayList<>(Arrays.asList(-60.004085993650335, -46.249771874999944, -36.40148437500135, -22.886831250001578, -8.39775000000147)));
            builder.append(new ArrayList<>(Arrays.asList(-69.00458537226298, -53.99168437499835, -44.21459687500029, -32.78760000000117, -17.627396875001434)));
            builder.append(new ArrayList<>(Arrays.asList(-70.00449459507554, -56.76171562499858, -43.38780000000024, -33.53242187500134, -20.640090625001296)));
            builder.append(new ArrayList<>(Arrays.asList(-70.00494857378972, -56.80333749999857, -43.41665625000154, -33.582031250001094, -20.773590625001443)));
            builder.append(new ArrayList<>(Arrays.asList(-70.00499396959763, -55.33433437499896, -44.850396875002, -34.82922500000137, -19.716681250001074)));
            builder.append(new ArrayList<>(Arrays.asList(-70.0049939902318, -58.13497812499857, -46.526240625001364, -31.294840625001566, -19.090171874999807)));
            builder.append(new ArrayList<>(Arrays.asList(-70.00499399229089, -56.493149999999105, -43.628506250001806, -33.88290312500148, -20.950887499999578)));
            builder.append(new ArrayList<>(Arrays.asList(-70.00499399229089, -58.81998437499879, -43.74528437500281, -31.753118750002557, -21.79080937499954)));
            builder.append(new ArrayList<>(Arrays.asList(-70.00499399229089, -58.35149062499834, -43.05281562500275, -32.23796875000258, -22.245231249999495)));
            builder.append(new ArrayList<>(Arrays.asList(-70.00499399229089, -55.222240624999515, -45.372640625001864, -34.033787500002234, -18.915256250000677)));
            builder.append(new ArrayList<>(Arrays.asList(-70.00499399229089, -58.495021874998656, -43.38252812500288, -31.858421875002815, -22.020599999999433)));
            Word<List<Double>> inputWord = builder.toWord();
            inputWord.stream().forEach(line -> line.add(line.get(4) - line.get(3)));
            input = new IOSignal<>(inputWord, inputWord);
            assert Objects.requireNonNull(input.getOutputSymbol(0)).size() == 6;
        }

        @Test
        void CC4() {
            STLCost costFunc1Atomic =
                    new STLOutputAtomic(5, STLOutputAtomic.Operation.gt, 8);
            TemporalOp<List<Double>> costFunc1Global =
                    new STLGlobally(costFunc1Atomic);
            STLCost costFunc1 =
                    new STLSub(costFunc1Global, 0, 2);
            STLCost costFunc2 =
                    new STLSub(new STLEventually(costFunc1), 0, 3);
            STLCost costFunc = new STLSub(new STLGlobally(costFunc2), 0, 6);

            RoSI robustness1Atomic = costFunc1Atomic.getRoSI(input);
            assertNotEquals(POSITIVE_INFINITY, robustness1Atomic.lowerBound);
            assertNotEquals(NEGATIVE_INFINITY, robustness1Atomic.lowerBound);

            RoSI robustness1Global = costFunc1Global.getRoSIRaw(input);
            assertEquals(1.8378218750033817, robustness1Global.lowerBound.doubleValue());
            assertEquals(1.8378218750033817, robustness1Global.upperBound.doubleValue());

            RoSI robustness1 = costFunc1.getRoSI(input);
            assertNotEquals(POSITIVE_INFINITY, robustness1.lowerBound);
            assertNotEquals(NEGATIVE_INFINITY, robustness1.lowerBound);

            RoSI robustness2 = costFunc2.getRoSI(input);
            assertNotEquals(POSITIVE_INFINITY, robustness2.upperBound);
            assertNotEquals(NEGATIVE_INFINITY, robustness2.upperBound);

            double robustness = costFunc.apply(input);

            assertNotEquals(POSITIVE_INFINITY, robustness);
            assertNotEquals(NEGATIVE_INFINITY, robustness);
        }
    }
}