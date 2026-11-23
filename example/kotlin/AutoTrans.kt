package net.maswag

/**
 * Returns a MATLAB command running the shared FalCAuN benchmark definition `benchmarks/simulink/[relativePath]`.
 *
 * The root of the FalCAuN repository is searched from the current working directory upwards.
 * The script is run by its absolute path, so the command works regardless of the current directory of MATLAB.
 * See `benchmarks/simulink/README.md`.
 */
fun benchmarkInitScript(relativePath: String): String {
    var root: java.io.File? = java.io.File("").absoluteFile
    while (root != null && !java.io.File(root, "benchmarks/simulink").isDirectory) {
        root = root.parentFile
    }
    val script = root?.let { java.io.File(it, "benchmarks/simulink/$relativePath") }
    require(script != null && script.isFile) {
        "benchmarks/simulink/$relativePath is not found. Run this example inside the FalCAuN repository."
    }
    return "run('${script.canonicalPath.replace("'", "''")}');"
}

// Initialization script for the automatic transmission model [Hoxha et al., ARCH@CPSWeek 2014].
// See benchmarks/simulink/AT/initAT.m for the details, e.g., the model and the unit conversion.
val initScript = benchmarkInitScript("AT/initAT.m")
val paramNames = listOf("throttle", "brake")
var signalStep = 1.0
val simulinkSimulationStep = 0.0025
