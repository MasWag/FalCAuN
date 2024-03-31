package net.maswag;

import net.automatalib.words.WordBuilder;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;
import java.util.Random;

import static java.lang.Double.POSITIVE_INFINITY;
import static org.junit.jupiter.api.Assertions.assertEquals;

class STLUntilTest {
    IOSignal signal;

    @BeforeEach
    void setUp() {
        Random random = new Random();
        int size = random.nextInt(32);
        WordBuilder<List<Double>> inputBuilder = new WordBuilder<>();
        WordBuilder<List<Double>> outputBuilder = new WordBuilder<>();

        for (int i = 0; i < size; i++) {
            inputBuilder.append(Collections.singletonList((random.nextDouble() - 0.5) * 2000));
            outputBuilder.append(Collections.singletonList((random.nextDouble() - 0.5) * 2000));
        }
        signal = new IOSignal(inputBuilder.toWord(), outputBuilder.toWord());
        assert signal.size() == size;
    }

    @Test
    void UntilEventually() {
        STLCost until = new STLUntil(new STLOutputAtomic(0, STLOutputAtomic.Operation.lt, POSITIVE_INFINITY),
                new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 0));
        STLCost eventually = new STLEventually(new STLOutputAtomic(0, STLOutputAtomic.Operation.gt, 0));
        RoSI untilRoSI = until.getRoSI(signal);
        RoSI eventuallyRoSI = eventually.getRoSI(signal);
        assertEquals(eventuallyRoSI.upperBound, untilRoSI.upperBound);
        assertEquals(eventuallyRoSI.lowerBound, untilRoSI.lowerBound);
    }
}