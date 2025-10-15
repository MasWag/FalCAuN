package net.maswag.falcaun;

import java.io.File;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import org.junit.jupiter.api.Test;

import net.automatalib.alphabet.Alphabet;
import net.automatalib.alphabet.Alphabets;
import net.automatalib.automaton.CompactTransition;
import net.automatalib.automaton.transducer.CompactMealy;
import net.automatalib.util.automaton.builder.AutomatonBuilders;
import net.automatalib.util.automaton.builder.MealyBuilder;

class DotMealyWrapperTest{
    @Test
    void dot1(){
        Alphabet<String> expectedSigma = Alphabets.fromList(Arrays.asList("a", "b", "c"));
        Alphabet<String> expectedGamma = Alphabets.fromList(Arrays.asList("x", "y", "z"));
        Set<String> expectedEdges =
            new HashSet<>( Arrays.asList("(0 : 1)[a/x]", "(1 : 2)[b/x]", "(2 : 3)[c/y]", "(3 : 4)[a/y]", "(4 : 0)[b/z]", "(__start0 : 0)null"));

        String path = new File(".").getAbsoluteFile().getParent() + "/src/test/java/net/maswag/falcaun/dotTestFiles/dotTest1";
        DotMealyWrapper wrapper = new DotMealyWrapper(path);
        Set<LabeledEdge> edgeSet = wrapper.graph.edgeSet();
        Alphabet<String> actualSigma = wrapper.sigma;
        Alphabet<String> actualGamma = wrapper.gamma;
        Set<String> actualEdges = new HashSet<>();
        for (LabeledEdge edge : edgeSet) {
            actualEdges.add(edge.toString());
        }

        assertEquals(expectedSigma, actualSigma);
        assertEquals(expectedGamma, actualGamma);
        assertEquals(expectedEdges, actualEdges);
    }

    void dot2(){
        Alphabet<String> expectedSigma = Alphabets.fromList(Arrays.asList("0", "1", "2", "3"));
        Alphabet<String> expectedGamma = Alphabets.fromList(Arrays.asList("0", "1", "2", "3"));
        Set<String> expectedEdges = new HashSet<>(
            Arrays.asList("(0 : 0)[0/0]", "(0 : 1)[0/1]", "(0 : 2)[0/2]", "(0 : 3)[0/3]",
                          "(1 : 0)[1/0]", "(1 : 1)[1/1]", "(1 : 2)[1/2]", "(1 : 3)[1/3]",
                          "(2 : 0)[2/0]", "(2 : 1)[2/1]", "(2 : 2)[2/2]", "(2 : 3)[2/3]",
                          "(3 : 0)[3/0]", "(3 : 1)[3/1]", "(3 : 2)[3/2]", "(3 : 3)[3/3]",
                          "(__start0 : 0)null")
        );

        String path = new File(".").getAbsoluteFile().getParent() + "/src/test/java/net/maswag/falcaun/dotTestFiles/dotTest2";
        DotMealyWrapper wrapper = new DotMealyWrapper(path);
        Set<LabeledEdge> edgeSet = wrapper.graph.edgeSet();
        Alphabet<String> actualSigma = wrapper.sigma;
        Alphabet<String> actualGamma = wrapper.gamma;
        Set<String> actualEdges = new HashSet<>();
        for (LabeledEdge edge : edgeSet) {
            actualEdges.add(edge.toString());
        }

        assertEquals(expectedSigma, actualSigma);
        assertEquals(expectedGamma, actualGamma);
        assertEquals(expectedEdges, actualEdges);
    }

    @Test
    void toMealy1(){
        Alphabet<String> sigma = Alphabets.fromList(Arrays.asList("a", "b", "c"));
        MealyBuilder<Integer,String, CompactTransition<String>, String, CompactMealy<String, String>> mealyBuilder
            = AutomatonBuilders.newMealy(sigma);
        CompactMealy<String, String> expected =
            mealyBuilder
            .from("1").on("b").withOutput("x").to("2")
            .from("2").on("c").withOutput("y").to("3")
            .from("4").on("b").withOutput("z").to("0")
            .from("0").on("a").withOutput("x").to("1")
            .from("3").on("a").withOutput("y").to("4")
            .withInitial("0")
            .create();

        String path = new File(".").getAbsoluteFile().getParent() + "/src/test/java/net/maswag/falcaun/dotTestFiles/dotTest1";
        DotMealyWrapper wrapper = new DotMealyWrapper(path);
        CompactMealy<String, String> actual = wrapper.createMealy();

        Map<Integer, Integer> expect_to_actual = new HashMap<>();
        Queue<Integer> unchecked = new LinkedList<>();
        unchecked.add(expected.getInitialState());
        expect_to_actual.put(expected.getInitialState(), actual.getInitialState());

        while(!unchecked.isEmpty()) {
            Integer current_state = unchecked.poll();
            for (String input: sigma) {
                CompactTransition<String> ex_transition = expected.getTransition(current_state, input);
                CompactTransition<String> ac_transition = actual.getTransition(expect_to_actual.get(current_state), input);
                if (ex_transition == null ^ ac_transition == null) assert(false);
                if (ex_transition != null) {
                    if (expect_to_actual.containsKey(ex_transition.getSuccId())) {
                        assertEquals(expect_to_actual.get(ex_transition.getSuccId()), ac_transition.getSuccId());
                    } else {
                        expect_to_actual.put(ex_transition.getSuccId(), ac_transition.getSuccId());
                        unchecked.add(ex_transition.getSuccId());
                    }
                }
            }
        }
    }

    @Test
    void toMealy2() {
        Alphabet<String> sigma = Alphabets.fromList(Arrays.asList("0", "1", "2", "3"));
        MealyBuilder<Integer,String, CompactTransition<String>, String, CompactMealy<String, String>> mealyBuilder
            = AutomatonBuilders.newMealy(sigma);
        CompactMealy<String, String> expected =
            mealyBuilder
            .from("0").on("0").withOutput("0").to("0")
            .from("0").on("1").withOutput("0").to("1")
            .from("0").on("2").withOutput("0").to("2")
            .from("0").on("3").withOutput("0").to("3")
            .from("1").on("0").withOutput("1").to("0")
            .from("1").on("1").withOutput("1").to("1")
            .from("1").on("2").withOutput("1").to("2")
            .from("1").on("3").withOutput("1").to("3")
            .from("2").on("0").withOutput("2").to("0")
            .from("2").on("1").withOutput("2").to("1")
            .from("2").on("2").withOutput("2").to("2")
            .from("2").on("3").withOutput("2").to("3")
            .from("3").on("0").withOutput("3").to("0")
            .from("3").on("1").withOutput("3").to("1")
            .from("3").on("2").withOutput("3").to("2")
            .from("3").on("3").withOutput("3").to("3")
            .withInitial("0")
            .create();

        String path = new File(".").getAbsoluteFile().getParent() + "/src/test/java/net/maswag/falcaun/dotTestFiles/dotTest2";
        DotMealyWrapper wrapper = new DotMealyWrapper(path);
        CompactMealy<String, String> actual = wrapper.createMealy();

        Map<Integer, Integer> expect_to_actual = new HashMap<>();
        Queue<Integer> unchecked = new LinkedList<>();
        unchecked.add(expected.getInitialState());
        expect_to_actual.put(expected.getInitialState(), actual.getInitialState());

        while(!unchecked.isEmpty()) {
            Integer current_state = unchecked.poll();
            for (String input: sigma) {
                CompactTransition<String> ex_transition = expected.getTransition(current_state, input);
                CompactTransition<String> ac_transition = actual.getTransition(expect_to_actual.get(current_state), input);
                if (ex_transition == null ^ ac_transition == null) assert(false);
                if (ex_transition != null) {
                    if (expect_to_actual.containsKey(ex_transition.getSuccId())) {
                        assertEquals(expect_to_actual.get(ex_transition.getSuccId()), ac_transition.getSuccId());
                    } else {
                        expect_to_actual.put(ex_transition.getSuccId(), ac_transition.getSuccId());
                        unchecked.add(ex_transition.getSuccId());
                    }
                }
            }
        }
    }
}