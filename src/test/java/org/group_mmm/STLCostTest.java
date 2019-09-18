package org.group_mmm;

import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.util.*;

import static java.lang.Double.POSITIVE_INFINITY;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

class STLCostTest {
    private List<String> concreteExpected;
    private List<String> abstractExpected;
    private List<STLCost> formulas;

    @BeforeEach
    void setUp() {
        concreteExpected = Arrays.asList(
                "[] ( signal(0) < 120.000000 )",
                "[] ( ( signal(2) == 3.000000 ) -> ( signal(0) > 20.000000 ) )"
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
        List<STLAtomic> atomics = new ArrayList<>();
        atomics.add(new STLAtomic(0, STLAtomic.Operation.lt, 120.0));
        atomics.add(new STLAtomic(2, STLAtomic.Operation.eq, 3));
        atomics.add(new STLAtomic(0, STLAtomic.Operation.gt, 20));
        for (STLAtomic atomic : atomics) {
            atomic.setAtomic(outputMapper, largest);
        }

        formulas = Arrays.asList(
                new STLGlobal(atomics.get(0)),
                new STLGlobal(new STLImply(atomics.get(1), atomics.get(2)))
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

    @Nested
    class Bug201906171356 {
        Word<List<Double>> input;

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
            input = builder.toWord();
            assert input.size() == 15;
        }

        @Test
        void ATExampleS4() {
            STLCost costFunc =
                    new STLOr(new STLSub(new STLGlobal(new STLAtomic(0, STLAtomic.Operation.lt, 100)), 0, 13),
                            new STLSub(new STLGlobal(new STLAtomic(0, STLAtomic.Operation.gt, 65.0)), 14, 14));
            assertNotEquals(POSITIVE_INFINITY, costFunc.apply(input));
        }

        @Test
        void ATExampleS4AndTextRepl() {
            STLCost costFuncExt =
                    new STLOr(new STLSub(new STLGlobal(new STLAtomic(0, STLAtomic.Operation.lt, 100)), 0, 13),
                            new STLSub(new STLGlobal(new STLAtomic(0, STLAtomic.Operation.gt, 65.0)), 14, 14));
            STLCost costFunc = STLCost.parseSTL("([]_[0,13] (signal(0) < 100)) || ([]_[14,14] (signal(0) > 65.0))");
            assertEquals(costFuncExt.apply(input), costFunc.apply(input));
        }
    }
}