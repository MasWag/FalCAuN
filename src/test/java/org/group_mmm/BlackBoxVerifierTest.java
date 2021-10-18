package org.group_mmm;

import de.learnlib.api.SUL;
import de.learnlib.api.oracle.MembershipOracle;
import de.learnlib.driver.util.MealySimulatorSUL;
import de.learnlib.oracle.membership.SULOracle;
import net.automatalib.automata.transducers.impl.compact.CompactMealy;
import net.automatalib.util.automata.builders.AutomatonBuilders;
import net.automatalib.words.Alphabet;
import net.automatalib.words.WordBuilder;
import net.automatalib.words.impl.ArrayAlphabet;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.mockito.Mockito.*;

class BlackBoxVerifierTest {
    private final Alphabet<String> inputAlphabet = new ArrayAlphabet<>("a");
    private List<String> properties;
    private BlackBoxVerifier verifier;
    StaticLTLList ltlList;
    MembershipOracle.MealyMembershipOracle<String, String> memOracle;
    SUL<String, String> sul;

    @BeforeEach
    void setUp() {
        properties = Arrays.asList("X X X output == \"2\"",
                "output == \"1\"",
                "[] (output == \"2\" -> X output == \"1\")",
                "X X output == \"2\"");
        CompactMealy<String, String> mealy = new CompactMealy<>(inputAlphabet);
        mealy = AutomatonBuilders.forMealy(mealy).
                withInitial("q0").
                from("q0").
                on("a").withOutput("1").to("q1").
                from("q1").
                on("a").withOutput("2").to("q0").
                create();
        sul = new MealySimulatorSUL<>(mealy);
        memOracle = new SULOracle<>(sul);
        ltlList = spy(new StaticLTLList(properties));
        ltlList.setMemOracle(memOracle);
        verifier = new BlackBoxVerifier(memOracle, sul, ltlList, inputAlphabet);
    }

    @Test
    void run() {
        assertFalse(verifier.run());
    }

    @Test
    void notifyFalsifiedProperty() {
        for (int i = 0; i < 4; i++) {
            doCallRealMethod().when(ltlList).notifyFalsifiedProperty(i);
        }
        assertFalse(verifier.run());
        verify(ltlList, times(0)).notifyFalsifiedProperty(0);
        verify(ltlList, times(0)).notifyFalsifiedProperty(1);
        verify(ltlList, times(0)).notifyFalsifiedProperty(2);
        verify(ltlList, times(1)).notifyFalsifiedProperty(3);
    }

    @Test
    void getCexProperty() {
        assertFalse(verifier.run());
        assertEquals(properties, verifier.getCexProperty());
    }

    @Test
    void getCexInput() {
        WordBuilder<String> expected = new WordBuilder<>();
        expected.add("a");
        expected.add("a");
        expected.add("a");

        assertFalse(verifier.run());
        System.out.println(verifier.getCexInput());
        assertEquals(expected.toWord(), verifier.getCexInput().stream().filter(Objects::nonNull).findFirst().orElse(null));
    }

    @Test
    void getCexOutput() {
        WordBuilder<String> expected = new WordBuilder<>();
        expected.add("1");
        expected.add("2");
        expected.add("1");

        assertFalse(verifier.run());
        System.out.println(verifier.getCexOutput());
        assertEquals(expected.toWord(), verifier.getCexOutput().stream().filter(Objects::nonNull).findFirst().orElse(null));
    }

    @Test
    void writeETFLearnedMealy() {
        assertFalse(verifier.run());
        String expected = "begin state\n" +
                "id:id\n" +
                "end state\n" +
                "begin edge\n" +
                "input:input\n" +
                "output:output\n" +
                "end edge\n" +
                "begin init\n" +
                "0\n" +
                "end init\n" +
                "begin sort id\n" +
                "\"s0\"\n" +
                "\"s1\"\n" +
                "end sort\n" +
                "begin trans\n" +
                "0/1 0 0\n" +
                "1/0 0 1\n" +
                "end trans\n" +
                "begin sort input\n" +
                "\"a\"\n" +
                "end sort\n" +
                "begin sort output\n" +
                "\"1\"\n" +
                "\"2\"\n" +
                "end sort\n";
        ByteArrayOutputStream stream = new ByteArrayOutputStream();
        verifier.writeETFLearnedMealy(stream);
        assertEquals(expected, stream.toString());
    }
}