package net.maswag.falcaun;

import de.learnlib.oracle.EquivalenceOracle.MealyEquivalenceOracle;
import de.learnlib.query.DefaultQuery;
import net.automatalib.automaton.transducer.MealyMachine;
import net.automatalib.word.Word;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Collection;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

class TimeoutEQOracleTest {

    @BeforeEach
    void setUp() {
        // no setup needed - each test creates its own instances
    }

    @Test
    void beforeTimeout_delegatesToOracle() {
        @SuppressWarnings("unchecked")
        MealyEquivalenceOracle<String, String> wrappedOracle = mock(MealyEquivalenceOracle.class);

        long[] fakeClock = {0};
        TimeoutEQOracle<String, String> timeoutOracle =
                new TimeoutEQOracle<>(wrappedOracle, 120, () -> fakeClock[0]);

        timeoutOracle.start();
        fakeClock[0] = 100_000_000_000L; // 100 seconds

        DefaultQuery<String, Word<String>> result = timeoutOracle.findCounterExample(null, null);

        verify(wrappedOracle).findCounterExample(isNull(), isNull());
    }

    @Test
    void atTimeoutBoundary_delegatesToOracle() {
        @SuppressWarnings("unchecked")
        MealyEquivalenceOracle<String, String> wrappedOracle = mock(MealyEquivalenceOracle.class);

        long[] fakeClock = {0};
        TimeoutEQOracle<String, String> timeoutOracle =
                new TimeoutEQOracle<>(wrappedOracle, 120, () -> fakeClock[0]);

        timeoutOracle.start();
        fakeClock[0] = 120_000_000_000L; // exactly 120 seconds

        timeoutOracle.findCounterExample(null, null);

        verify(wrappedOracle).findCounterExample(isNull(), isNull());
    }

    @Test
    void afterTimeout_returnsNull() {
        @SuppressWarnings("unchecked")
        MealyEquivalenceOracle<String, String> wrappedOracle = mock(MealyEquivalenceOracle.class);

        long[] fakeClock = {0};
        TimeoutEQOracle<String, String> timeoutOracle =
                new TimeoutEQOracle<>(wrappedOracle, 120, () -> fakeClock[0]);

        timeoutOracle.start();
        fakeClock[0] = 121_000_000_000L; // 121 seconds

        DefaultQuery<String, Word<String>> result = timeoutOracle.findCounterExample(null, null);

        assertNull(result);
        verifyNoInteractions(wrappedOracle);
    }
}
