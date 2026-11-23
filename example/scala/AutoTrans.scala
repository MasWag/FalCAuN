package net.maswag.falcaun

// Scala 3 definitions used by ATS1.sc

/** MATLAB command running the shared FalCAuN benchmark definition `benchmarks/simulink/<relativePath>`.
  *
  * The root of the FalCAuN repository is searched from the current working directory upwards.
  * The script is run by its absolute path, so the command works regardless of the current directory of MATLAB.
  * See `benchmarks/simulink/README.md`.
  */
def benchmarkInitScript(relativePath: String): String =
  var root = new java.io.File("").getAbsoluteFile
  while root != null && !new java.io.File(root, "benchmarks/simulink").isDirectory do
    root = root.getParentFile
  val script = if root == null then null else new java.io.File(root, s"benchmarks/simulink/$relativePath")
  require(script != null && script.isFile,
    s"benchmarks/simulink/$relativePath is not found. Run this example inside the FalCAuN repository.")
  "run('" + script.getCanonicalPath.replace("'", "''") + "');"

// Initialization script for the automatic transmission model [Hoxha et al., ARCH@CPSWeek 2014].
// See benchmarks/simulink/AT/initAT.m for the details, e.g., the model and the unit conversion.
val initScript: String = benchmarkInitScript("AT/initAT.m")

// Parameter names for Simulink inputs
val paramNames: java.util.List[String] = java.util.Arrays.asList("throttle", "brake")

// Sampling step for input signal (seconds)
var signalStep: Double = 1.0

// Fixed-step size used in Simulink simulation (seconds)
val simulinkSimulationStep: Double = 0.0025
