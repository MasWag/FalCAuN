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

import java.util.Arrays;
import java.util.List;
import java.util.Objects;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

class BlackBoxVerifierTest {
    private final Alphabet<String> inputAlphabet = new ArrayAlphabet<>("a");
    private List<String> properties;
    private SUL<String, String> sul;
    private BlackBoxVerifier verifier;

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
        this.sul = new MealySimulatorSUL<>(mealy);
        MembershipOracle.MealyMembershipOracle<String, String> memOracle = new SULOracle<>(sul);
        verifier = new BlackBoxVerifier(memOracle, this.sul, properties, inputAlphabet);
    }

    @Test
    void run() {
        assertFalse(verifier.run());
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
        assertEquals(expected.toWord(), verifier.getCexOutput().stream().filter(Objects::nonNull).findFirst().orElse(null));
    }
}