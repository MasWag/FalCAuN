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
import java.util.*;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.mockito.Mockito.*;

class BlackBoxVerifierTest {
    private final Alphabet<String> inputAlphabet = new ArrayAlphabet<>("a");
    StaticSTLList stlList;
    private BlackBoxVerifier verifier;
    private List<STLCost> falsifiedProperties;
    MembershipOracle.MealyMembershipOracle<String, String> memOracle;
    SUL<String, String> sul;

    @BeforeEach
    void setUp() {
        List<STLOutputAtomic> events = new ArrayList<>();
        events.add(new STLOutputAtomic(0, STLAbstractAtomic.Operation.lt, 1.0));
        events.add(new STLOutputAtomic(0, STLAbstractAtomic.Operation.gt, 1.0));
        events.get(0).setAtomic(Collections.singletonList(Collections.singletonMap('a', 1.0)), Collections.singletonList('b'));
        events.get(1).setAtomic(Collections.singletonList(Collections.singletonMap('a', 1.0)), Collections.singletonList('b'));

        List<STLCost> properties = Arrays.asList(
                new STLNext(new STLNext(new STLNext(events.get(1), true), true), true),
                events.get(0),
                new STLGlobal(new STLImply(events.get(1), new STLNext(events.get(0), true))),
                new STLNext(new STLNext(events.get(1), true), true));
        falsifiedProperties = new ArrayList<>();
        falsifiedProperties.add(properties.get(3));
        CompactMealy<String, String> mealy = new CompactMealy<>(inputAlphabet);
        mealy = AutomatonBuilders.forMealy(mealy).
                withInitial("q0").
                from("q0").
                on("a").withOutput("a").to("q1").
                from("q1").
                on("a").withOutput("b").to("q0").
                create();
        sul = new MealySimulatorSUL<>(mealy);
        memOracle = new SULOracle<>(sul);
        stlList = spy(new StaticSTLList(properties));
        stlList.setMemOracle(memOracle);
        verifier = new BlackBoxVerifier(memOracle, sul, stlList, inputAlphabet);
        stlList.stream();
    }

    @Test
    void run() {
        assertFalse(verifier.run());
    }

    @Test
    void notifyFalsifiedProperty() {
        doCallRealMethod().when(stlList).notifyFalsifiedProperty(Arrays.asList(0, 1, 2, 3));
        assertFalse(verifier.run());
        verify(stlList, times(1)).notifyFalsifiedProperty(Collections.singletonList(0));
        verify(stlList, times(0)).notifyFalsifiedProperty(Collections.singletonList(1));
        verify(stlList, times(0)).notifyFalsifiedProperty(Collections.singletonList(2));
        verify(stlList, times(0)).notifyFalsifiedProperty(Collections.singletonList(3));
        verify(stlList, times(0)).notifyFalsifiedProperty(Arrays.asList(0, 1, 2, 3));
    }

    @Test
    void getCexProperty() {
        assertFalse(verifier.run());
        assertEquals(falsifiedProperties.stream().map(Objects::toString).collect(Collectors.toList()), verifier.getCexProperty());
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
        expected.add("a");
        expected.add("b");
        expected.add("a");

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
                "\"a\"\n" +
                "\"b\"\n" +
                "end sort\n";
        ByteArrayOutputStream stream = new ByteArrayOutputStream();
        verifier.writeETFLearnedMealy(stream);
        assertEquals(expected, stream.toString());
    }
}