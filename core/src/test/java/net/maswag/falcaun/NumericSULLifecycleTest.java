package net.maswag.falcaun;

import net.automatalib.word.Word;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import net.maswag.falcaun.signal.IOSignal;

import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests of the lifecycle of {@link NumericSUL}, i.e., {@code pre()}, {@code step()}, {@code post()}, and {@code execute()}.
 */
class NumericSULLifecycleTest {
    private CountingNumericSUL sul;

    private static Word<List<Double>> input(double... values) {
        Word<List<Double>> result = Word.epsilon();
        for (double value : values) {
            result = result.append(Collections.singletonList(value));
        }
        return result;
    }

    @BeforeEach
    void setUp() {
        sul = new CountingNumericSUL();
    }

    @Test
    void executeRunsOneSession() throws Exception {
        IOSignal<List<Double>> result = sul.execute(input(1.0, 2.0, 0.0));
        assertEquals(List.of("pre", "step", "step", "step", "post"), sul.getEvents());
        assertEquals(input(1.0, 2.0, 0.0), result.getInputSignal());
        assertEquals(input(1.0, 3.0, 3.0), result.getOutputSignal());
        assertEquals(1, sul.getExecutionCount());
    }

    @Test
    void repeatedExecutionsAreIndependent() throws Exception {
        IOSignal<List<Double>> first = sul.execute(input(1.0, 2.0));
        IOSignal<List<Double>> second = sul.execute(input(1.0, 2.0));
        assertEquals(first.getOutputSignal(), second.getOutputSignal());
        assertEquals(List.of("pre", "step", "step", "post", "pre", "step", "step", "post"), sul.getEvents());
        assertEquals(2, sul.getExecutionCount());
    }

    @Test
    void stepWiseSessionMatchesExecute() throws Exception {
        sul.pre();
        double first = sul.step(Collections.singletonList(1.0)).getOutputSignal().get(0);
        double second = sul.step(Collections.singletonList(2.0)).getOutputSignal().get(0);
        sul.post();
        assertEquals(List.of(1.0, 3.0), List.of(first, second));
        assertEquals(input(1.0, 3.0), sul.execute(input(1.0, 2.0)).getOutputSignal());
    }

    @Test
    void postIsCalledWhenStepFails() {
        sul.setFailAtStep(1);
        assertThrows(RuntimeException.class, () -> sul.execute(input(1.0, 2.0, 0.0)));
        assertEquals(List.of("pre", "step", "step", "post"), sul.getEvents());
        // The SUL can be executed again after a failure
        sul.setFailAtStep(-1);
        sul.getEvents().clear();
        assertDoesNotThrow(() -> sul.execute(input(1.0)));
        assertEquals(List.of("pre", "step", "post"), sul.getEvents());
    }

    @Test
    void postIsNotCalledWhenPreFails() {
        sul.setFailAtPre(true);
        assertThrows(RuntimeException.class, () -> sul.execute(input(1.0)));
        assertEquals(List.of("pre"), sul.getEvents());
    }
}
