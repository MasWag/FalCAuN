package org.group_mmm;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.util.*;
import java.util.stream.Collectors;

import static org.group_mmm.STLCost.parseSTL;
import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.Matchers.containsInAnyOrder;
import static org.junit.jupiter.api.Assertions.*;

class StaticSTLListTest {
    private AdaptiveSTLUpdater properties;

    @Nested
    class AutoTransTest {
        List<Map<Character, Double>> inputMapper;
        List<Map<Character, Double>> outputMapper;
        List<Character> largest;

        @BeforeEach
        void setUp() {
            // Construct the mapper
            {
                Map<Character, Double> mapper1 = new HashMap<>();
                mapper1.put('a', 00.0);
                mapper1.put('b', 100.0);
                Map<Character, Double> mapper2 = new HashMap<>();
                mapper2.put('a', 0.0);
                mapper2.put('b', 325.0);
                inputMapper = new ArrayList<>(Arrays.asList(mapper1, mapper2));
            }
            {
                Map<Character, Double> mapper1 = new HashMap<>();
                mapper1.put('a', 120.0);
                Map<Character, Double> mapper2 = new HashMap<>();
                mapper2.put('a', 4750.0);
                Map<Character, Double> mapper3 = new HashMap<>();

                outputMapper = new ArrayList<>(Arrays.asList(mapper1, mapper2, mapper3));
                largest = new ArrayList<>(Arrays.asList('b', 'b', 'a'));
            }
        }

        @Nested
        class AT1AndAT2Test {
            List<String> expectedStlStringList;
            List<STLCost> stlList;


            @BeforeEach
            void setUp() {
                List<String> stlStringList = Arrays.asList(
                        "alw_[0, 20] (signal(0) < 120)",
                        "alw_[0, 10] (signal(1) < 4750)");
                stlList = stlStringList.stream().map(stlString ->
                        parseSTL(stlString, inputMapper, outputMapper, largest)).collect(Collectors.toList());
                expectedStlStringList = stlList.stream().map(Object::toString).collect(Collectors.toList());
                properties = new StaticSTLList(stlList);
            }

            @Test
            void size() {
                assertEquals(2, properties.size());
                assertEquals(2, properties.getSTLProperties().size());
                assertThat("All the given properties should be reported as counterexamples",
                        properties.getSTLProperties().stream().map(Object::toString).collect(Collectors.toList()),
                        containsInAnyOrder(expectedStlStringList.get(0), expectedStlStringList.get(1)));
            }

            @Test
            void reset() {
                properties.reset();
                assertEquals(2, properties.size());
                assertEquals(2, properties.getSTLProperties().size());
                assertThat("All the given properties should be reported as counterexamples",
                        properties.getSTLProperties().stream().map(Object::toString).collect(Collectors.toList()),
                        containsInAnyOrder(expectedStlStringList.get(0), expectedStlStringList.get(1)));
            }
        }
    }
}