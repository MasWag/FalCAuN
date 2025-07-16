package net.maswag.falcaun.parser;

import com.pholser.junit.quickcheck.From;
import com.pholser.junit.quickcheck.Property;
import com.pholser.junit.quickcheck.runner.JUnitQuickcheck;

import net.maswag.falcaun.IOSignal;
import net.maswag.falcaun.IOSignalGenerator;
import net.maswag.falcaun.parser.TemporalEventually.STLEventually;
import net.maswag.falcaun.parser.TemporalLogic.STLCost;
import net.maswag.falcaun.parser.TemporalUntil.STLUntil;
import org.junit.runner.RunWith;

import java.util.List;

import static java.lang.Double.POSITIVE_INFINITY;
import static org.junit.jupiter.api.Assertions.assertEquals;

@RunWith(JUnitQuickcheck.class)
public class STLUntilTest {
    @Property
    public void UntilEventually(@From(IOSignalGenerator.class) IOSignal<List<Double>> signal) {
        STLCost until = new STLUntil(new STLOutputAtomic(0, STLOutputAtomic.Operation.lt, POSITIVE_INFINITY),
                new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 0));
        STLCost eventually = new STLEventually(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 0));
        RoSI untilRoSI = until.getRoSI(signal);
        RoSI eventuallyRoSI = eventually.getRoSI(signal);
        assertEquals(eventuallyRoSI.upperBound, untilRoSI.upperBound);
        assertEquals(eventuallyRoSI.lowerBound, untilRoSI.lowerBound);
    }
}
