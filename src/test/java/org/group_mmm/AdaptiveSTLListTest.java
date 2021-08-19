package org.group_mmm;

import java.util.*;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class AdaptiveSTLListTest {
    STLCost stl;
    AdaptiveSTLList adaptiveSTLList;

    @Test
    void strengthenEventually() {
        stl = STLCost.parseSTL("[] (<> output(0) < 1.5)");
        adaptiveSTLList = new AdaptiveSTLList(stl);

        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("[] ([] (output(0) < 1.5))"),
                STLCost.parseSTL("[] (<> (output(0) < 1.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("[] (<> ([] (output(0) < 1.5)))"),
                STLCost.parseSTL("[] (<> (output(0) < 1.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("[] ([] (<> (output(0) < 1.5)))"),
                STLCost.parseSTL("[] (<> (output(0) < 1.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Collections.singletonList(
                STLCost.parseSTL("[] (<> (output(0) < 1.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        assertTrue(adaptiveSTLList.getSTLProperties().isEmpty());
    }

    @Test
    void strengthenOr() {
        stl = STLCost.parseSTL("(output(0) < 1.5) && ((output(1) > 2.0) || (output(2) < 2.5))");
        adaptiveSTLList = new AdaptiveSTLList(stl);

        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 1.5) && ((output(1) > 2.0) && (output(2) < 2.5))"),
                STLCost.parseSTL("(output(0) < 1.5) && ((output(1) > 2.0) || (output(2) < 2.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Collections.singletonList(
                STLCost.parseSTL("(output(0) < 1.5) && ((output(1) > 2.0) || (output(2) < 2.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        assertTrue(adaptiveSTLList.getSTLProperties().isEmpty());
    }

    @Test
    void strengthenUntil() {
        stl = STLCost.parseSTL("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)");
        adaptiveSTLList = new AdaptiveSTLList(stl);
        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(([] (output(0) < 3.0)) && ([] (output(1) > 3.5))) && (output(2) < 4.0)"),
                STLCost.parseSTL("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(([] (output(0) < 3.0)) && (<> ([] (output(1) > 3.5)))) && (output(2) < 4.0)"),
                STLCost.parseSTL("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(([] (output(0) < 3.0)) && ([] (<> (output(1) > 3.5)))) && (output(2) < 4.0)"),
                STLCost.parseSTL("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Collections.singletonList(
                STLCost.parseSTL("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        assertTrue(adaptiveSTLList.getSTLProperties().isEmpty());
    }

    @Test
    void strengthenGlobalInterval() {
        stl = STLCost.parseSTL("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)");
        adaptiveSTLList = new AdaptiveSTLList(stl);

        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([] (output(0) < 4.5)) && (output(1) > 5.0)"),
                STLCost.parseSTL("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 17] (output(0) < 4.5)) && (output(1) > 5.0)"),
                STLCost.parseSTL("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 10] (output(0) < 4.5)) && (output(1) > 5.0)"),
                STLCost.parseSTL("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 7] (output(0) < 4.5)) && (output(1) > 5.0)"),
                STLCost.parseSTL("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 5] (output(0) < 4.5)) && (output(1) > 5.0)"),
                STLCost.parseSTL("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Collections.singletonList(
                STLCost.parseSTL("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        assertTrue(adaptiveSTLList.getSTLProperties().isEmpty());
    }

    @Test
    void strengthenEventuallyInterval() {
        stl = STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))");
        adaptiveSTLList = new AdaptiveSTLList(stl);

        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && ([] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && ([]_[1, 16] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && ([]_[1, 9] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && ([]_[1, 5] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && ([]_[1, 3] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 2] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 6] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 8] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 9] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        assertTrue(adaptiveSTLList.getSTLProperties().isEmpty());
    }

    @Test
    void strengthenNext() {
        stl = STLCost.parseSTL("(X (output(0) < 6.5)) && (output(1) > 7.0)");
        adaptiveSTLList = new AdaptiveSTLList(stl);

        ArrayList<STLCost> expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([] (output(0) < 6.5)) && (output(1) > 7.0)"),
                STLCost.parseSTL("(X (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 15] (output(0) < 6.5)) && (output(1) > 7.0)"),
                STLCost.parseSTL("(X (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 8] (output(0) < 6.5)) && (output(1) > 7.0)"),
                STLCost.parseSTL("(X (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 4] (output(0) < 6.5)) && (output(1) > 7.0)"),
                STLCost.parseSTL("(X (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 2] (output(0) < 6.5)) && (output(1) > 7.0)"),
                STLCost.parseSTL("(X (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(X (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(0);
        assertTrue(adaptiveSTLList.getSTLProperties().isEmpty());
    }
}
