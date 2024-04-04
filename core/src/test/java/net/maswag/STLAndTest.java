package net.maswag;

import com.pholser.junit.quickcheck.Property;
import com.pholser.junit.quickcheck.generator.InRange;
import com.pholser.junit.quickcheck.runner.JUnitQuickcheck;
import net.automatalib.word.Word;
import org.junit.runner.RunWith;

import java.util.Collections;
import java.util.List;

import static java.lang.Math.min;
import static org.junit.jupiter.api.Assertions.assertEquals;
import net.maswag.TemporalLogic.STLCost;
import net.maswag.TemporalAnd.STLAnd;

@RunWith(JUnitQuickcheck.class)
public class STLAndTest {
    private final STLCost formula = new STLAnd(
            new STLOutputAtomic(0, STLAbstractAtomic.Operation.gt, 20.0),
            new STLOutputAtomic(0, STLAbstractAtomic.Operation.lt, 100.0));

    @Property
    public void andIsMin(@InRange(min = "0.0", max = "200.0") double value) {
        Word<List<Double>> outputSignal = Word.fromLetter(Collections.singletonList(value));
        Word<List<Double>> inputSignal = Word.fromLetter(Collections.emptyList());
        IOSignal signal = new IOSignal(inputSignal, outputSignal);
        double result = formula.apply(signal);
        assertEquals(min(value - 20.0, 100.0 - value), result);
    }
}
