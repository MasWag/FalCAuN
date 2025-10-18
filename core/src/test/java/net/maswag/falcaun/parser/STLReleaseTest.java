package net.maswag.falcaun.parser;

import com.pholser.junit.quickcheck.From;
import com.pholser.junit.quickcheck.Property;
import com.pholser.junit.quickcheck.runner.JUnitQuickcheck;

import net.maswag.falcaun.IOSignal;
import net.maswag.falcaun.IOSignalGenerator;
import net.maswag.falcaun.parser.TemporalGlobally.STLGlobally;
import net.maswag.falcaun.parser.TemporalLogic.STLCost;
import net.maswag.falcaun.parser.TemporalRelease.STLRelease;
import net.maswag.falcaun.parser.TemporalUntil.STLUntil;
import net.maswag.falcaun.parser.TemporalNot.STLNot;
import org.junit.runner.RunWith;

import java.util.List;

import static java.lang.Double.POSITIVE_INFINITY;
import static org.junit.jupiter.api.Assertions.assertEquals;

@RunWith(JUnitQuickcheck.class)
public class STLReleaseTest {
    @Property
    public void releaseGlobally(@From(IOSignalGenerator.class) IOSignal<List<Double>> signal) {
        STLCost release = new STLRelease(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, POSITIVE_INFINITY),
                new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 0));
        STLCost globally = new STLGlobally(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 0));
        RoSI releaseRoSI = release.getRoSI(signal);
        RoSI globallyRoSI = globally.getRoSI(signal);
        assertEquals(globallyRoSI.upperBound, releaseRoSI.upperBound);
        assertEquals(globallyRoSI.lowerBound, releaseRoSI.lowerBound);
    }

    @Property
    public void releaseUntil(@From(IOSignalGenerator.class) IOSignal<List<Double>> signal) {
        STLCost release = new STLRelease(new STLInputAtomic(0, STLInputAtomic.Operation.lt, 0),
                new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 0));
        STLCost until = new STLNot(new STLUntil(
                new STLNot(new STLInputAtomic(0, STLInputAtomic.Operation.lt, 0)),
                new STLNot(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 0))));
        RoSI releaseRoSI = release.getRoSI(signal);
        RoSI untilRoSI = until.getRoSI(signal);
        assertEquals(untilRoSI.upperBound, releaseRoSI.upperBound);
        assertEquals(untilRoSI.lowerBound, releaseRoSI.lowerBound);
    }
}
