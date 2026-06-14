package net.maswag.falcaun.python;

import org.junit.jupiter.api.Assumptions;

final class JepTestSupport {
    private JepTestSupport() {
    }

    static void assumePythonExecutableSet() {
        var pythonExecutable = System.getenv("PYTHONEXECUTABLE");
        Assumptions.assumeTrue(pythonExecutable != null && !pythonExecutable.isBlank(),
                "PYTHONEXECUTABLE must point to a Python environment with Jep installed");
    }
}
