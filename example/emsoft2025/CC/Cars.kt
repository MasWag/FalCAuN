/*****h* CC/Cars
 *  NAME
 *   Cars.kt
 *  DESCRIPTION
 *   Common configuration for the chasing cars model [Hoxha et al., ARCH@CPSWeek 2014].
 *  AUTHOR
 *   Masaki Waga
 *  HISTORY
 *    - 2024/04/26: Initial version
 *  COPYRIGHT
 *   Copyright (c) 2024 Masaki Waga
 *   Released under the MIT license
 *   https://opensource.org/licenses/mit-license.php
 *
 *  PORTABILITY
 *   This script assumes the following:
 *   - FalCAuN is installed, for example, by mvn install.
 *   - The environment variable MATLAB_HOME is set to the root directory of MATLAB, e.g., /Applications/MATLAB_R2024a.app/ or /usr/local/MATLAB/R2024a.
 *
 ********/

@file:Import("../Common.kt") // Import the common configuration

import net.maswag.falcaun.*

// Define the configuration of the chasing cars model
val initScript = "mdl = 'cars'; load_system(mdl);"
val paramNames = listOf("throttle", "brake")
var signalStep = 5.0
val simulinkSimulationStep = 0.0025

// Define the input mapper
val throttleValues = listOf(0.0, 1.0)
val brakeValues = listOf(0.0, 1.0)
val inputMapper = InputMapperReader.make(listOf(throttleValues, brakeValues))

// Define the output signal names
val y1 = "signal(0)"
val y2 = "signal(1)"
val y3 = "signal(2)"
val y4 = "signal(3)"
val y5 = "signal(4)"

// Define the function to scale the duration
fun scaleDuration(duration: Int): Int {
    return (duration / signalStep).toInt()
}
