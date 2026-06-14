package net.maswag.falcaun.python;

import org.junit.jupiter.api.Assumptions;

import java.nio.file.Files;
import java.nio.file.Path;

final class JepTestSupport {
    private JepTestSupport() {
    }

    static void assumePythonExecutableSet() {
        var pythonExecutable = System.getenv("PYTHONEXECUTABLE");
        Assumptions.assumeTrue(pythonExecutable != null && !pythonExecutable.isBlank(),
                "PYTHONEXECUTABLE must point to a Python environment with Jep installed");
        var executablePath = Path.of(pythonExecutable);
        Assumptions.assumeTrue(executablePath.isAbsolute(),
                "PYTHONEXECUTABLE must be an absolute path to avoid Maven module working-directory issues");
        Assumptions.assumeTrue(Files.isExecutable(executablePath),
                "PYTHONEXECUTABLE must point to an executable Python with Jep installed");
    }
}
