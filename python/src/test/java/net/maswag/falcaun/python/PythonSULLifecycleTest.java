package net.maswag.falcaun.python;

import net.automatalib.word.Word;
import net.maswag.falcaun.NumericSUL;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collections;
import java.util.List;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests of the lifecycle of the Python-based numeric SULs.
 * The Python scripts record the lifecycle events to {@link #EVENT_LOG}.
 */
class PythonSULLifecycleTest {
    private static final Path EVENT_LOG = Path.of("./target/python_lifecycle_events.txt");
    private static final String STEP_SCRIPT = "./src/test/resources/lifecycle_sul.py";
    private static final String EXEC_SCRIPT = "./src/test/resources/lifecycle_sul_with_exec.py";
    private static final String CONTINUOUS_SCRIPT = "./src/test/resources/lifecycle_continuous_sul.py";

    @BeforeAll
    static void assumeJepAvailable() {
        JepTestSupport.assumePythonExecutableSet();
    }

    @BeforeEach
    void setUp() throws IOException {
        Files.createDirectories(EVENT_LOG.getParent());
        Files.deleteIfExists(EVENT_LOG);
    }

    private static List<String> events() throws IOException {
        return Files.exists(EVENT_LOG) ? Files.readAllLines(EVENT_LOG) : List.of();
    }

    private static Word<List<Double>> input(double... values) {
        Word<List<Double>> result = Word.epsilon();
        for (double value : values) {
            result = result.append(Collections.singletonList(value));
        }
        return result;
    }

    private static NumericSUL create(String script) throws Exception {
        return script.equals(CONTINUOUS_SCRIPT) ? new PythonContinuousNumericSUL(script, 1.0) : new PythonNumericSUL(script);
    }

    private static List<String> expectedSession(String script, int steps) {
        List<String> result = new java.util.ArrayList<>();
        result.add("pre");
        if (script.equals(EXEC_SCRIPT)) {
            result.add("exec");
        } else {
            result.addAll(Collections.nCopies(steps, "step"));
        }
        result.add("post");
        return result;
    }

    @ParameterizedTest
    @ValueSource(strings = {STEP_SCRIPT, EXEC_SCRIPT, CONTINUOUS_SCRIPT})
    void executeRunsOneSession(String script) throws Exception {
        try (NumericSUL sul = create(script)) {
            var result = sul.execute(input(1.0, 2.0, 3.0));
            assertEquals(input(1.0, 3.0, 6.0), result.getOutputSignal());
            assertEquals(expectedSession(script, 3), events());
            assertEquals(1, sul.getExecutionCount());

            Files.deleteIfExists(EVENT_LOG);
            assertEquals(input(1.0, 3.0, 6.0), sul.execute(input(1.0, 2.0, 3.0)).getOutputSignal());
            assertEquals(expectedSession(script, 3), events());
            assertEquals(2, sul.getExecutionCount());
        }
        assertEquals("close", events().get(events().size() - 1));
    }

    @ParameterizedTest
    @ValueSource(strings = {STEP_SCRIPT, EXEC_SCRIPT, CONTINUOUS_SCRIPT})
    void postIsCalledWhenExecutionFails(String script) throws Exception {
        try (NumericSUL sul = create(script)) {
            assertThrows(Exception.class, () -> sul.execute(input(1.0, -1.0, 3.0)));
            List<String> expected = new java.util.ArrayList<>(List.of("pre"));
            expected.add(script.equals(EXEC_SCRIPT) ? "exec" : "step");
            if (!script.equals(EXEC_SCRIPT)) {
                expected.add("step");
            }
            expected.add("post");
            assertEquals(expected, events());

            // The SUL can be executed again after a failure
            Files.deleteIfExists(EVENT_LOG);
            assertEquals(input(1.0, 3.0), sul.execute(input(1.0, 2.0)).getOutputSignal());
            assertEquals(expectedSession(script, 2), events());
        }
    }

    @ParameterizedTest
    @ValueSource(strings = {STEP_SCRIPT, CONTINUOUS_SCRIPT})
    void stepWiseSession(String script) throws Exception {
        try (NumericSUL sul = create(script)) {
            sul.pre();
            assertEquals(List.of(1.0), sul.step(List.of(1.0)).getOutputSignal());
            assertEquals(List.of(3.0), sul.step(List.of(2.0)).getOutputSignal());
            sul.post();
            assertEquals(List.of("pre", "step", "step", "post"), events());
        }
    }

    /**
     * Each thread has its own interpreter and Python objects. Using the SUL in another thread must not affect the
     * Python objects used by the original thread.
     */
    @ParameterizedTest
    @ValueSource(strings = {STEP_SCRIPT, EXEC_SCRIPT})
    void executeOnAnotherThread(String script) throws Exception {
        try (NumericSUL sul = create(script)) {
            AtomicReference<Word<List<Double>>> output = new AtomicReference<>();
            AtomicReference<Throwable> error = new AtomicReference<>();
            Thread thread = new Thread(() -> {
                try {
                    output.set(sul.execute(input(1.0, 2.0)).getOutputSignal());
                } catch (Throwable e) {
                    error.set(e);
                }
            });
            thread.start();
            thread.join();
            assertNull(error.get());
            assertEquals(input(1.0, 3.0), output.get());
            // The SUL still works in the original thread
            assertEquals(input(1.0, 3.0), sul.execute(input(1.0, 2.0)).getOutputSignal());
        }
    }
}
