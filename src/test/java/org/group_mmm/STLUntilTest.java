package org.group_mmm;

import net.automatalib.words.Word;
import net.automatalib.words.WordBuilder;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;
import java.util.Random;

import static java.lang.Double.POSITIVE_INFINITY;
import static org.junit.jupiter.api.Assertions.assertEquals;

class STLUntilTest {
    Word<List<Double>> input;

    @BeforeEach
    void setUp() {
        Random random = new Random();
        int size = random.nextInt(32);
        WordBuilder<List<Double>> builder = new WordBuilder<>();
        for (int i = 0; i < size; i++) {
            builder.append(Collections.singletonList((random.nextDouble() - 0.5) * 2000));
        }
        input = builder.toWord();
        assert input.size() == size;
    }

    @Test
    void UntilEventually() {
        STLCost until = new STLUntil(new STLAtomic(0, STLAtomic.Operation.lt, POSITIVE_INFINITY),
                new STLAtomic(0, STLAtomic.Operation.gt, 0));
        STLCost eventually = new STLEventually(new STLAtomic(0, STLAtomic.Operation.gt, 0));
        STLCost.RoSI untilRoSI = until.getRoSI(input);
        STLCost.RoSI eventuallyRoSI = eventually.getRoSI(input);
        assertEquals(eventuallyRoSI.upperBound, untilRoSI.upperBound);
        assertEquals(eventuallyRoSI.lowerBound, untilRoSI.lowerBound);
    }
}