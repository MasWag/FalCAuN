package net.maswag.falcaun;

import net.maswag.falcaun.parser.STLFactory;
import net.maswag.falcaun.parser.TemporalLogic.STLCost;
import org.junit.jupiter.api.Test;

import java.util.*;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for the {@link NumericSULMapperWithSGA} class.
 * 
 * @author Tsubasa Matsumoto {@literal <tsubari96061@gmail.com>}
 */
class SGAMapperTest {
    @Test
    void Mapper(){
        List<String> formulas = Arrays.asList(
        "signal(0) < 10.0",
            "signal(1) > 4.2",
            "signal(1) == -20",
            "(signal(0) < 10.0) || (signal(1) == 2.2)",
            "(signal(0) < -1.0) -> (signal(1) == 2.2)",
            "X (signal(1) == -20)",
            "[] (signal(1) == -20)",
            "<> (signal(1) == -20)",
            "alw_[0,2] (signal(1) == -20)",
            "ev_[10,20] (signal(1) == -20)",
            "[] ((signal(2) != 4 && X (signal(2) == 4)) -> []_[0,1] (signal(2) == 4))",
                "[] ((signal(2) == 4) -> signal(0) > 10)", // S2
            "alw((signal(1) < 4.2) || (X (signal(1) > 4.2)))", // S5
            "(signal(0) > 10) U (signal(1) < 4.2)", // Until
            "(signal(0) > 10) R (signal(1) < 4.2)", // Release
            "(!(signal(0) > -1.0)) || (alw_[0,5] signal(1) < 4.2)"
        );

        STLFactory factory = new STLFactory();
        Map<Character, Double> velocityMap = new HashMap<>();
        velocityMap.put('a', -1.0);
        velocityMap.put('b', 10.0);

        Map<Character, Double> rotationMap = new HashMap<>();
        rotationMap.put('a', -20.0);
        rotationMap.put('b', 2.2);
        rotationMap.put('c', 4.2);

        Map<Character, Double> gearMap = new HashMap<>();
        gearMap.put('a', 4.0);

        List<Map<Character, Double>> inputMapper = Collections.emptyList();
        List<Map<Character, Double>> outputMapper = Arrays.asList(velocityMap, rotationMap, gearMap);
        List<Character> largest = Arrays.asList('c', 'd', 'b');
        SignalMapper sigMap = new ExtendedSignalMapper();

        List<List<String>> expectedList = Arrays.asList(
            Arrays.asList("aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "caa", "caa", "caa", "caa",
                               "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "caa", "caa", "caa", "caa"),
            Arrays.asList("aaa", "aaa", "aaa", "ada", "aaa", "aaa", "aaa", "ada", "aaa", "aaa", "aaa", "ada",
                               "aaa", "aaa", "aaa", "ada", "aaa", "aaa", "aaa", "ada", "aaa", "aaa", "aaa", "ada"),
            Arrays.asList("aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba",
                               "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba"),
            Arrays.asList("aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "caa", "aaa", "caa", "caa",
                               "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "caa", "aaa", "caa", "caa"),
            Arrays.asList("aaa", "aba", "aaa", "aaa", "aba", "aba", "aba", "aba", "aba", "aba", "aba", "aba",
                               "aaa", "aba", "aaa", "aaa", "aba", "aba", "aba", "aba", "aba", "aba", "aba", "aba"),
            Arrays.asList("aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba",
                               "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba"),
            Arrays.asList("aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba",
                               "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba"),
            Arrays.asList("aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba",
                               "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba"),
            Arrays.asList("aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba",
                               "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba"),
            Arrays.asList("aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba",
                               "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba", "aaa", "aba", "aba", "aba"),
            Arrays.asList("aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa",
                               "aab", "aab", "aab", "aab", "aab", "aab", "aab", "aab", "aab", "aab", "aab", "aab"),
            Arrays.asList("aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aaa", "aab", "aab", "aab", "aab",
                               "aab", "aab", "aab", "aab", "aab", "aab", "aab", "aab", "aab", "aab", "aab", "aab"),
            Arrays.asList("aaa", "aaa", "aaa", "ada", "aaa", "aaa", "aaa", "ada", "aaa", "aaa", "aaa", "ada",
                               "aaa", "aaa", "aaa", "ada", "aaa", "aaa", "aaa", "ada", "aaa", "aaa", "aaa", "ada"),
            Arrays.asList("aaa", "aaa", "aaa", "ada", "aaa", "aaa", "aaa", "ada", "aaa", "aaa", "aaa", "cda",
                               "aaa", "aaa", "aaa", "ada", "aaa", "aaa", "aaa", "ada", "aaa", "aaa", "aaa", "cda"),
            Arrays.asList("aaa", "aaa", "aaa", "ada", "aaa", "aaa", "aaa", "ada", "caa", "caa", "caa", "ada",
                               "aaa", "aaa", "aaa", "ada", "aaa", "aaa", "aaa", "ada", "caa", "caa", "caa", "ada"),
            Arrays.asList("aaa", "aaa", "aaa", "ada", "baa", "baa", "baa", "bda", "baa", "baa", "baa", "bda",
                               "aaa", "aaa", "aaa", "ada", "baa", "baa", "baa", "bda", "baa", "baa", "baa", "bda")
        );

        List<IOSignalPiece<List<Double>>> inputs = Arrays.asList(
                new IOSignalPiece<List<Double>>(null, Arrays.asList(-1.0, -20.0, 0.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(-1.0, 2.2, 0.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(-1.0, 4.2, 0.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(-1.0, 20.0, 0.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(10.0, -20.0, 0.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(10.0, 2.2, 0.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(10.0, 4.2, 0.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(10.0, 20.0, 0.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(20.0, -20.0, 0.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(20.0, 2.2, 0.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(20.0, 4.2, 0.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(20.0, 20.0, 0.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(-1.0, -20.0, 5.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(-1.0, 2.2, 5.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(-1.0, 4.2, 5.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(-1.0, 20.0, 5.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(10.0, -20.0, 5.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(10.0, 2.2, 5.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(10.0, 4.2, 5.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(10.0, 20.0, 5.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(20.0, -20.0, 5.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(20.0, 2.2, 5.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(20.0, 4.2, 5.)),
                new IOSignalPiece<List<Double>>(null, Arrays.asList(20.0, 20.0, 5.))
        );
        for (int i = 0; i < formulas.size(); i++) {
            System.out.println(i);
            STLCost formula = factory.parse(formulas.get(i), inputMapper, outputMapper, largest);
            NumericSULMapperWithSGA mapper = new NumericSULMapperWithSGA(inputMapper, largest, outputMapper, sigMap, Arrays.asList(formula), false);
            List<String> expected = expectedList.get(i);
            for (int j = 0; j < expected.size(); j++){
                assertEquals(expected.get(j), mapper.mapOutput(inputs.get(j)));
            }
        }
    }
}
