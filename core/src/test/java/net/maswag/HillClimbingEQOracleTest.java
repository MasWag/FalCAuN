package net.maswag;

import net.automatalib.word.Word;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Random;

class HillClimbingEQOracleTest {
    private HillClimbingEQOracle eqOracle;

    @BeforeEach
    void setUp() {
        eqOracle = new HillClimbingEQOracle(null, 10, new Random(0), 100, 5, 2, false);
        eqOracle.symbolList = Arrays.asList("a", "b", "c", "d", "e");
    }

    @Test
    void createNextGeneration() {
        List<Word<String>> input = Collections.singletonList(Word.fromList(Arrays.asList("a", "b")));
        List<Word<String>> output1 = eqOracle.createNextGeneration(input);
        List<Word<String>> output2 = eqOracle.createNextGeneration(input);
        Assertions.assertNotEquals(output1, output2);
    }
}