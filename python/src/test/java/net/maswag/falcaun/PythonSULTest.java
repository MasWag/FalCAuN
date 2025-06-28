package net.maswag.falcaun;

import org.junit.jupiter.api.*;

import static org.junit.jupiter.api.Assertions.*;

class PythonSULTest {
    static final String mealyScript = "./src/test/resources/mealy_python.py";

    @Test
    void mealyTest() throws Exception {
        try (var sul = new PythonSUL<String, String>(mealyScript, String.class)) {
            sul.pre();

            assertEquals("p", sul.step("a"));
            assertEquals("q", sul.step("a"));

            assertNull(sul.step(null));

            sul.post();
            assertFalse(sul.canFork());
            assertThrows(UnsupportedOperationException.class, () -> sul.fork());
        }
    }
}
