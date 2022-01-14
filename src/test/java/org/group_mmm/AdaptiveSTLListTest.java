package org.group_mmm;

import java.util.*;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

class AdaptiveSTLListTest {
    List<STLCost> stlList;
    AdaptiveSTLList adaptiveSTLList;

    @Test
    void strengthenEventually() {
        stlList = Collections.singletonList(STLCost.parseSTL("[] (<> output(0) < 1.5)"));
        adaptiveSTLList = new AdaptiveSTLList(stlList);

        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("[] ([] (output(0) < 1.5))"),
                STLCost.parseSTL("[] (<> (output(0) < 1.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("[] (<> ([] (output(0) < 1.5)))"),
                STLCost.parseSTL("[] (<> (output(0) < 1.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("[] ([] (<> (output(0) < 1.5)))"),
                STLCost.parseSTL("[] (<> (output(0) < 1.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Collections.singletonList(
                STLCost.parseSTL("[] (<> (output(0) < 1.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        assertTrue(adaptiveSTLList.getSTLProperties().isEmpty());
    }

    @Test
    void strengthenOr() {
        stlList = Collections.singletonList(STLCost.parseSTL("(output(0) < 1.5) && ((output(1) > 2.0) || (output(2) < 2.5))"));
        adaptiveSTLList = new AdaptiveSTLList(stlList);

        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 1.5) && ((output(1) > 2.0) && (output(2) < 2.5))"),
                STLCost.parseSTL("(output(0) < 1.5) && ((output(1) > 2.0) || (output(2) < 2.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Collections.singletonList(
                STLCost.parseSTL("(output(0) < 1.5) && ((output(1) > 2.0) || (output(2) < 2.5))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        assertTrue(adaptiveSTLList.getSTLProperties().isEmpty());
    }

    @Test
    void strengthenUntil() {
        stlList = Collections.singletonList(STLCost.parseSTL("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)"));
        adaptiveSTLList = new AdaptiveSTLList(stlList);
        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(([] (output(0) < 3.0)) && ([] (output(1) > 3.5))) && (output(2) < 4.0)"),
                STLCost.parseSTL("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(([] (output(0) < 3.0)) && (<> ([] (output(1) > 3.5)))) && (output(2) < 4.0)"),
                STLCost.parseSTL("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(([] (output(0) < 3.0)) && ([] (<> (output(1) > 3.5)))) && (output(2) < 4.0)"),
                STLCost.parseSTL("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Collections.singletonList(
                STLCost.parseSTL("((output(0) < 3.0) U (output(1) > 3.5)) && (output(2) < 4.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        assertTrue(adaptiveSTLList.getSTLProperties().isEmpty());
    }

    @Test
    void strengthenGlobalInterval() {
        stlList = Collections.singletonList(STLCost.parseSTL("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)"));
        adaptiveSTLList = new AdaptiveSTLList(stlList);

        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([] (output(0) < 4.5)) && (output(1) > 5.0)"),
                STLCost.parseSTL("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 17] (output(0) < 4.5)) && (output(1) > 5.0)"),
                STLCost.parseSTL("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 10] (output(0) < 4.5)) && (output(1) > 5.0)"),
                STLCost.parseSTL("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 7] (output(0) < 4.5)) && (output(1) > 5.0)"),
                STLCost.parseSTL("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 5] (output(0) < 4.5)) && (output(1) > 5.0)"),
                STLCost.parseSTL("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Collections.singletonList(
                STLCost.parseSTL("([]_[0, 4] (output(0) < 4.5)) && (output(1) > 5.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        assertTrue(adaptiveSTLList.getSTLProperties().isEmpty());
    }

    @Test
    void strengthenEventuallyInterval() {
        stlList = Collections.singletonList(STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))"));
        adaptiveSTLList = new AdaptiveSTLList(stlList);

        List<STLCost> expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && ([] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && ([]_[1, 16] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && ([]_[1, 9] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && ([]_[1, 5] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && ([]_[1, 3] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 2] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 6] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 8] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 9] (output(1) > 6.0))"),
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(output(0) < 5.5) && (<>_[2, 10] (output(1) > 6.0))")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        assertTrue(adaptiveSTLList.getSTLProperties().isEmpty());
    }

    @Test
    void strengthenNext() {
        stlList = Collections.singletonList(STLCost.parseSTL("(X (output(0) < 6.5)) && (output(1) > 7.0)"));
        adaptiveSTLList = new AdaptiveSTLList(stlList);

        ArrayList<STLCost> expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([] (output(0) < 6.5)) && (output(1) > 7.0)"),
                STLCost.parseSTL("(X (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 15] (output(0) < 6.5)) && (output(1) > 7.0)"),
                STLCost.parseSTL("(X (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 8] (output(0) < 6.5)) && (output(1) > 7.0)"),
                STLCost.parseSTL("(X (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 4] (output(0) < 6.5)) && (output(1) > 7.0)"),
                STLCost.parseSTL("(X (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[0, 2] (output(0) < 6.5)) && (output(1) > 7.0)"),
                STLCost.parseSTL("(X (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("(X (output(0) < 6.5)) && (output(1) > 7.0)")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        assertTrue(adaptiveSTLList.getSTLProperties().isEmpty());
    }

    @Test
    void strengthenCompoundSTL() {
        stlList = Collections.singletonList(STLCost.parseSTL("([]_[3, 10] (output(1) > 2.2)) && ([] (<> output(2) < 5.1))"));
        adaptiveSTLList = new AdaptiveSTLList(stlList);
        ArrayList<STLCost> expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )"),
                STLCost.parseSTL("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( [] ( output(2) < 5.100000 ) )"),
                STLCost.parseSTL("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[2, 20] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )"),
                STLCost.parseSTL("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( [] ( output(2) < 5.100000 ) )"),
                STLCost.parseSTL("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(0,1));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[2, 15] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )"),
                STLCost.parseSTL("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( <> ( [] ( output(2) < 5.100000 ) ) )"),
                STLCost.parseSTL("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Collections.singletonList(1));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[2, 15] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )"),
                STLCost.parseSTL("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( [] ( <> ( output(2) < 5.100000 ) ) )"),
                STLCost.parseSTL("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(0,1));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[2, 12] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )"),
                STLCost.parseSTL("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(0));
        expected = new ArrayList<>(Arrays.asList(
                STLCost.parseSTL("([]_[2, 11] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )"),
                STLCost.parseSTL("([]_[3, 10] ( output(1) > 2.200000 )) && [] ( <> ( output(2) < 5.100000 ) )")
        ));
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(0,1));
        assertTrue(adaptiveSTLList.getSTLProperties().isEmpty());
    }

    @Test
    void strengthenMultipleSTLs() {
        stlList = Arrays.asList(
                STLCost.parseSTL("(output(0) > 2.0) || (output(1) < 2.5)"),
                STLCost.parseSTL("(output(0) > 7.0) U (output(1) < 6.6)"),
                STLCost.parseSTL("(X (output(0) < 3.5)) && (<> output(1) > 9.0)"));
        adaptiveSTLList = new AdaptiveSTLList(stlList);
        List<STLCost> expected = Arrays.asList(
                STLCost.parseSTL("(output(0) > 2.0) && (output(1) < 2.5)"),
                STLCost.parseSTL("([] output(0) > 7.0) && ([] output(1) < 6.6)"),
                STLCost.parseSTL("([] (output(0) < 3.5)) && (<> output(1) > 9.0)"),
                STLCost.parseSTL("(X (output(0) < 3.5)) && ([] output(1) > 9.0)"),
                STLCost.parseSTL("(output(0) > 2.0) || (output(1) < 2.5)"),
                STLCost.parseSTL("(output(0) > 7.0) U (output(1) < 6.6)"),
                STLCost.parseSTL("(X (output(0) < 3.5)) && (<> output(1) > 9.0)")
        );
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(0,2,3));
        expected = Arrays.asList(
                STLCost.parseSTL("([] output(0) > 7.0) && ([] output(1) < 6.6)"),
                STLCost.parseSTL("([]_[0, 15] (output(0) < 3.5)) && (<> output(1) > 9.0)"),
                STLCost.parseSTL("(X (output(0) < 3.5)) && (<> ([] output(1) > 9.0))"),
                STLCost.parseSTL("(output(0) > 2.0) || (output(1) < 2.5)"),
                STLCost.parseSTL("(output(0) > 7.0) U (output(1) < 6.6)"),
                STLCost.parseSTL("(X (output(0) < 3.5)) && (<> output(1) > 9.0)")
        );
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(0,2,4));
        expected = Arrays.asList(
                STLCost.parseSTL("([]_[0, 15] (output(0) < 3.5)) && (<> output(1) > 9.0)"),
                STLCost.parseSTL("(X (output(0) < 3.5)) && ([] (<> output(1) > 9.0))"),
                STLCost.parseSTL("(output(0) > 2.0) || (output(1) < 2.5)"),
                STLCost.parseSTL("(X (output(0) < 3.5)) && (<> output(1) > 9.0)")
        );
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(0,1));
        expected = Arrays.asList(
                STLCost.parseSTL("([]_[0, 8] (output(0) < 3.5)) && (<> output(1) > 9.0)"),
                STLCost.parseSTL("(output(0) > 2.0) || (output(1) < 2.5)"),
                STLCost.parseSTL("(X (output(0) < 3.5)) && (<> output(1) > 9.0)")
        );
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(1));
        expected = Arrays.asList(
                STLCost.parseSTL("([]_[0, 8] (output(0) < 3.5)) && (<> output(1) > 9.0)"),
                STLCost.parseSTL("(X (output(0) < 3.5)) && (<> output(1) > 9.0)")
        );
        assertEquals(expected.toString(), adaptiveSTLList.getSTLProperties().toString());

        adaptiveSTLList.notifyFalsifiedProperty(Arrays.asList(0, 1));
        assertTrue(adaptiveSTLList.getSTLProperties().isEmpty());
    }
}
