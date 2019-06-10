package org.group_mmm;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

class STLCostTest {
    private List<String> concreteExpected;
    private List<String> abstractExpected;
    private List<STLCost> formulas;

    @BeforeEach
    void setUp() {
        concreteExpected = Arrays.asList(
                "[] ( signal(0) < 120.000000 )",
                "[] ( ( signal(2) == 3.000000 ) -> ( signal(0) > 20.000000 ) )"
        );
        formulas = Arrays.asList(
                new STLGlobal(new STLAtomic(0, STLAtomic.Operation.lt, 120.0)),
                new STLGlobal(new STLImply(new STLAtomic(2, STLAtomic.Operation.eq, 3),
                        new STLAtomic(0, STLAtomic.Operation.gt, 20)))
        );

        assert concreteExpected.size() == formulas.size();
    }

    @Test
    void toStringTest() {
        for (int i = 0; i < concreteExpected.size(); i++) {
            assertEquals(concreteExpected.get(i), formulas.get(i).toString());
        }
    }
}