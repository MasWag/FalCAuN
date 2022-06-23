package org.group_mmm;

import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.mapper.MappedSUL;
import de.learnlib.oracle.membership.SULOracle;
import net.automatalib.words.Alphabet;
import net.automatalib.words.Word;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.*;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;

class SimulinkMembershipOracleTest {
    private final String PWD = System.getenv("PWD");
    private final String initScript = "cd " + PWD + "/src/test/resources/MATLAB; initAFC;";
    /*
       The range should be as follows.
	  - Pedal_Angle: [8.8 90.0]
      - Engine_Speed: [900.0 1100.0]
     */
    private final List<String> paramNames = new ArrayList<>(Arrays.asList("Pedal Angle", "Engine Speed"));
    private final Double signalStep = 10.0;
    private List<String> properties;
    private SimulinkSULMapper mapper;
    private List<Function<SimulinkSUL.IOSignalPiece, Double>> sigMap = new ArrayList<>();
    private SimulinkSUL simulink;
    private MappedSUL<String, String, List<Double>, SimulinkSUL.IOSignalPiece> mappedSimulink;
    private MembershipOracle.MealyMembershipOracle<String, String> sulOracle, directOracle;
    private Alphabet<String> abstractInputAlphabet;
    private Alphabet<List<Double>> concreteInputAlphabet;

    @BeforeEach
    void setUp() throws Exception {
        // [] (velocity < 30)
        properties = new ArrayList<>(Collections.singletonList("[] (output == \"a00\")"));

        // Construct the mapper
        List<Map<Character, Double>> inputMapper;
        List<Map<Character, Double>> outputMapper;
        List<Character> largest;

        {
            Map<Character, Double> mapper1 = new HashMap<>();
            mapper1.put('a', 00.0);
            mapper1.put('b', 80.0);
            Map<Character, Double> mapper2 = new HashMap<>();
            mapper2.put('a', 0.0);
            mapper2.put('b', 9000.0);
            inputMapper = new ArrayList<>(Arrays.asList(mapper1, mapper2));
        }
        {
            Map<Character, Double> mapper1 = new HashMap<>();
            mapper1.put('a', 10.0);
            mapper1.put('b', 20.0);
            Map<Character, Double> mapper2 = new HashMap<>();
            Map<Character, Double> mapper3 = new HashMap<>();

            outputMapper = new ArrayList<>(Arrays.asList(mapper1, mapper2, mapper3));
            largest = new ArrayList<>(Arrays.asList('c', '0', '0'));
        }
        this.mapper = new SimulinkSULMapper(inputMapper, largest, outputMapper, new SignalMapper(sigMap));
        this.simulink = new SimulinkSUL(initScript, paramNames, signalStep);
        this.concreteInputAlphabet = mapper.constructConcreteAlphabet();
        this.abstractInputAlphabet = mapper.constructAbstractAlphabet();


        this.mappedSimulink = new MappedSUL<>(mapper, simulink);
        this.sulOracle = new SULOracle<>(this.mappedSimulink);
        this.directOracle = new SimulinkMembershipOracle(this.simulink, this.mapper);
    }

    @Test
    void processQueries() {
        List<Word<String>> inputs = Arrays.asList(
                Word.fromList(Arrays.asList("aa", "ab")),
                Word.fromList(Arrays.asList("bb", "bb", "aa")),
                Word.fromList(Collections.singletonList("bb")));
        for (Word<String> input : inputs) {
            Word<String> sulOutput = this.sulOracle.answerQuery(input);
            Word<String> directOutput = this.directOracle.answerQuery(input);
            assertEquals(sulOutput, directOutput);
        }
    }
}