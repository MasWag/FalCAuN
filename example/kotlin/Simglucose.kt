package net.maswag

import net.maswag.falcaun.python.PythonNumericSUL

/**
 * Common utilities/constants for simglucose examples.
 */
val initScript = "./simglucose_example.py"
var signalStep = 1.0
// Each step corresponds to 30 minutes.
val stepDuration = 30.0

// Name of signals
val mealSize = "input(0)"
val bg = "output(0)"
val insulin = "output(1)"
val min_bg = "output(2)"
val max_bg = "output(3)"
val min_delta_bg = "output(4)"
val max_delta_bg = "output(5)"

/**
 * Create a Python-backed SUL for simglucose.
 */
fun makeSimglucoseSUL(): PythonNumericSUL = PythonNumericSUL(initScript)

