package org.group_mmm;

import com.pholser.junit.quickcheck.Property;
import com.pholser.junit.quickcheck.generator.InRange;
import com.pholser.junit.quickcheck.runner.JUnitQuickcheck;
import net.automatalib.words.Word;
import org.junit.runner.RunWith;

import java.util.Collections;
import java.util.List;

import static java.lang.Math.min;
import static org.junit.jupiter.api.Assertions.assertEquals;

@RunWith(JUnitQuickcheck.class)
public class STLAndTest {
    private STLCost formula = new STLAnd(
            new STLAtomic(0, STLAtomic.Operation.gt, 20.0),
            new STLAtomic(0, STLAtomic.Operation.lt, 100.0));

    @Property
    public void andIsMin(@InRange(min = "0.0", max = "200.0") double value) {
        Word<List<Double>> input = Word.fromLetter(Collections.singletonList(value));
        double result = formula.apply(input);
        assertEquals(min(value - 20.0, 100.0 - value), result);
    }
}
