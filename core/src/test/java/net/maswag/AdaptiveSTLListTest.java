package net.maswag;

import net.maswag.TemporalLogic.STLCost;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.hamcrest.collection.IsIterableContainingInAnyOrder.containsInAnyOrder;
import static org.junit.jupiter.api.Assertions.assertEquals;
class AdaptiveSTLListTest {
    List<STLCost> stlList;
    AdaptiveSTLList<List<Double>> adaptiveSTLList;
    int timeWindow = 30;

    @Test
    void strengthenEventually() {
        STLFactory factory = new STLFactory();
        stlList = Collections.singletonList(factory.parse("[] (<> output(0) < 1.5)"));
        adaptiveSTLList = new AdaptiveSTLList<>(stlList, timeWindow);

        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                factory.parse("[] ([] (output(0) < 1.5))"),
                factory.parse("[] (<> (output(0) < 1.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("[] (<> (output(0) < 1.5))"),
                factory.parse("[] (<> ([] (output(0) < 1.5)))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("[] (<> (output(0) < 1.5))"),
                factory.parse("[] ([] (<> (output(0) < 1.5)))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Collections.singletonList(
                factory.parse("[] (<> (output(0) < 1.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        assertEquals(stlList.toString(), adaptiveSTLList.getSTLProperties().toString());
    }

    @Test
    void strengthenOr() {
        STLFactory factory = new STLFactory();
        stlList = Collections.singletonList(factory.parse("(output(0) < 1.5) && ((output(1) > 2.0) || (output(2) < 2.5))"));
        adaptiveSTLList = new AdaptiveSTLList<>(stlList, timeWindow);

        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                factory.parse("(output(0) < 1.5) && ((output(1) > 2.0) && (output(2) < 2.5))"),
                factory.parse("(output(0) < 1.5) && ((output(1) > 2.0) || (output(2) < 2.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Collections.singletonList(
                factory.parse("(output(0) < 1.5) && ((output(1) > 2.0) || (output(2) < 2.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        assertEquals(stlList.toString(), adaptiveSTLList.getSTLProperties().toString());
    }

    @Test
    void strengthenUntil() {
        STLFactory factory = new STLFactory();
        stlList = Collections.singletonList(factory.parse("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)"));
        adaptiveSTLList = new AdaptiveSTLList<>(stlList, timeWindow);
        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                factory.parse("(([] (output(0) < 3.0)) && ([] (output(1) > 3.5))) && (output(2) < 4.0)"),
                factory.parse("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)"),
                factory.parse("(([] (output(0) < 3.0)) && (<> ([] (output(1) > 3.5)))) && (output(2) < 4.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)"),
                factory.parse("(([] (output(0) < 3.0)) && ([] (<> (output(1) > 3.5)))) && (output(2) < 4.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Collections.singletonList(
                factory.parse("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        assertEquals(stlList.toString(), adaptiveSTLList.getSTLProperties().toString());
    }

    @Test
    void strengthenGlobalInterval() {
        STLFactory factory = new STLFactory();
        stlList = Collections.singletonList(factory.parse("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)"));
        adaptiveSTLList = new AdaptiveSTLList<>(stlList, timeWindow);

        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                factory.parse("([] (output(0) < 4.5)) && (output(1) > 5.0)"),
                factory.parse("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)"),
                factory.parse("([]_[0, 17] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)"),
                factory.parse("([]_[0, 10] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)"),
                factory.parse("([]_[0, 7] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)"),
                factory.parse("([]_[0, 5] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Collections.singletonList(
                factory.parse("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        assertEquals(stlList.toString(), adaptiveSTLList.getSTLProperties().toString());
    }

    @Test
    void strengthenEventuallyInterval() {
        STLFactory factory = new STLFactory();
        stlList = Collections.singletonList(factory.parse("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))"));
        adaptiveSTLList = new AdaptiveSTLList<>(stlList, timeWindow);

        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                factory.parse("(output(0) < 5.5) && ([] (output(1) > 6.0))"),
                factory.parse("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))"),
                factory.parse("(output(0) < 5.5) && ([]_[1, 16] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))"),
                factory.parse("(output(0) < 5.5) && ([]_[1, 9] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))"),
                factory.parse("(output(0) < 5.5) && ([]_[1, 5] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))"),
                factory.parse("(output(0) < 5.5) && ([]_[1, 3] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))"),
                factory.parse("(output(0) < 5.5) && (<>_[2, 2] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))"),
                factory.parse("(output(0) < 5.5) && (<>_[2, 6] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))"),
                factory.parse("(output(0) < 5.5) && (<>_[2, 8] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))"),
                factory.parse("(output(0) < 5.5) && (<>_[2, 9] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Collections.singletonList(
                factory.parse("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        assertEquals(stlList.toString(), adaptiveSTLList.getSTLProperties().toString());
    }

    @Test
    void strengthenNext() {
        STLFactory factory = new STLFactory();
        stlList = Collections.singletonList(factory.parse("(X (output(0) < 6.5)) && (output(1) > 7.0)"));
        adaptiveSTLList = new AdaptiveSTLList<>(stlList, timeWindow);

        ArrayList<STLCost> expected = new ArrayList<>(Arrays.asList(
                factory.parse("([] (output(0) < 6.5)) && (output(1) > 7.0)"),
                factory.parse("(X (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("(X (output(0) < 6.5)) && (output(1) > 7.0)"),
                factory.parse("([]_[0, 15] (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("(X (output(0) < 6.5)) && (output(1) > 7.0)"),
                factory.parse("([]_[0, 8] (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("(X (output(0) < 6.5)) && (output(1) > 7.0)"),
                factory.parse("([]_[0, 4] (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("(X (output(0) < 6.5)) && (output(1) > 7.0)"),
                factory.parse("([]_[0, 2] (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Collections.singletonList(
                factory.parse("(X (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        assertThat(stlList.stream().map(Object::toString).collect(Collectors.toList()),
                containsInAnyOrder(adaptiveSTLList.getSTLProperties().stream().map(Object::toString).toArray()));
    }

    @Test
    void strengthenCompoundSTL() {
        STLFactory factory = new STLFactory();
        stlList = Collections.singletonList(factory.parse("([]_[3, 10] (output(1) > 2.2)) && ([] (<> output(2) < 5.1))"));
        adaptiveSTLList = new AdaptiveSTLList<>(stlList, timeWindow);
        ArrayList<STLCost> expected = new ArrayList<>(Arrays.asList(
                factory.parse("([] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )"),
                factory.parse("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( [] ( output(2) < 5.100000 ) )"),
                factory.parse("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( [] ( output(2) < 5.100000 ) )"),
                factory.parse("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )"),
                factory.parse("([]_[2, 20] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(0, 2));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )"),
                factory.parse("([]_[2, 15] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )"),
                factory.parse("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( <> ( [] ( output(2) < 5.100000 ) ) )")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(2));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )"),
                factory.parse("([]_[2, 15] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )"),
                factory.parse("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( [] ( <> ( output(2) < 5.100000 ) ) )")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(1, 2));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )"),
                factory.parse("([]_[2, 12] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                factory.parse("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )"),
                factory.parse("([]_[2, 11] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(0, 1));
        assertEquals(stlList.toString(), adaptiveSTLList.getSTLProperties().toString());
    }

    @Test
    void strengthenMultipleSTLs() {
        STLFactory factory = new STLFactory();
        stlList = Arrays.asList(
                factory.parse("(output(0) > 2.0) || (output(1) < 2.5)"),
                factory.parse("(output(0) > 7.0) U (output(1) < 6.6)"),
                factory.parse("(X (output(0) < 3.5)) && (<> output(1) > 9.0)"));
        adaptiveSTLList = new AdaptiveSTLList<>(stlList, timeWindow);
        List<STLCost> expected = Arrays.asList(
                factory.parse("(output(0) > 2.0) && (output(1) < 2.5)"),
                factory.parse("([] output(0) > 7.0) && ([] output(1) < 6.6)"),
                factory.parse("([] (output(0) < 3.5)) && (<> output(1) > 9.0)"),
                factory.parse("(X (output(0) < 3.5)) && ([] output(1) > 9.0)"),
                factory.parse("(output(0) > 2.0) || (output(1) < 2.5)"),
                factory.parse("(output(0) > 7.0) U (output(1) < 6.6)"),
                factory.parse("(X (output(0) < 3.5)) && (<> output(1) > 9.0)")
        );
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(0, 2, 3));
        expected = Arrays.asList(
                factory.parse("([] output(0) > 7.0) && ([] output(1) < 6.6)"),
                factory.parse("(output(0) > 2.0) || (output(1) < 2.5)"),
                factory.parse("(output(0) > 7.0) U (output(1) < 6.6)"),
                factory.parse("(X (output(0) < 3.5)) && (<> output(1) > 9.0)"),
                factory.parse("([]_[0, 15] (output(0) < 3.5)) && (<> output(1) > 9.0)"),
                factory.parse("(X (output(0) < 3.5)) && (<> ([] output(1) > 9.0))")
        );
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(0, 2, 5));
        expected = Arrays.asList(
                factory.parse("(output(0) > 2.0) || (output(1) < 2.5)"),
                factory.parse("(output(0) > 7.0) U (output(1) < 6.6)"),
                factory.parse("(X (output(0) < 3.5)) && (<> output(1) > 9.0)"),
                factory.parse("([]_[0, 15] (output(0) < 3.5)) && (<> output(1) > 9.0)"),
                factory.parse("(X (output(0) < 3.5)) && ([] (<> output(1) > 9.0))")
        );
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(3, 4));
        expected = Arrays.asList(
                factory.parse("(output(0) > 2.0) || (output(1) < 2.5)"),
                factory.parse("(output(0) > 7.0) U (output(1) < 6.6)"),
                factory.parse("(X (output(0) < 3.5)) && (<> output(1) > 9.0)"),
                factory.parse("([]_[0, 8] (output(0) < 3.5)) && (<> output(1) > 9.0)")
        );
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = Arrays.asList(
                factory.parse("(output(0) > 2.0) || (output(1) < 2.5)"),
                factory.parse("(output(0) > 7.0) U (output(1) < 6.6)"),
                factory.parse("(X (output(0) < 3.5)) && (<> output(1) > 9.0)"),
                factory.parse("([]_[0, 8] (output(0) < 3.5)) && (<> output(1) > 9.0)")
        );
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(2, 3));
        assertEquals(stlList.toString(), adaptiveSTLList.getSTLProperties().toString());
    }
}
