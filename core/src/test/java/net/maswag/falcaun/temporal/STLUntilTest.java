package net.maswag.falcaun.temporal;

import com.pholser.junit.quickcheck.From;
import com.pholser.junit.quickcheck.Property;
import com.pholser.junit.quickcheck.runner.JUnitQuickcheck;

import net.maswag.falcaun.signal.IOSignal;
import net.maswag.falcaun.signal.IOSignalGenerator;
import net.maswag.falcaun.temporal.TemporalEventually.STLEventually;
import net.maswag.falcaun.temporal.TemporalLogic.STLCost;
import net.maswag.falcaun.temporal.TemporalUntil.STLUntil;
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
