#!/usr/bin/env kscript

// Import the common utilities and constants
@file:Import("./Common.kt")
// Import the constants for AutoTrans
@file:Import("./AutoTrans.kt")
// This script depends on FalCAuN-core and FalCAuN-matlab
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT", "net.maswag.falcaun:FalCAuN-matlab:1.0-SNAPSHOT")
// We assume that the MATLAB_HOME environment variable is set
@file:KotlinOptions("-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64")

import net.maswag.falcaun.*
import net.maswag.falcaun.parser.STLFactory
import net.maswag.falcaun.simulink.SimulinkSUL
import kotlin.streams.toList

// Define the input and output mappers
val throttleValues = listOf(0.0, 100.0)
val brakeValues = listOf(0.0, 325.0)
val inputMapper = InputMapperReader.make(listOf(throttleValues, brakeValues))
val velocityValues = listOf(20.0, 22.5, 25.0, 27.5, 30.0, null)
val accelerationValues = listOf(null)
val gearValues = listOf(2.0, 3.0, null)
val outputMapperReader = OutputMapperReader(listOf(velocityValues, accelerationValues, gearValues))
val signalMapper = SimpleSignalMapper()
val mapper = NumericSULMapper(inputMapper, outputMapperReader, signalMapper)

// Define the STL properties
val stlList = parseStlList(
    listOf(
        "[]((signal(2) == 3) -> signal(0) > 20)",
        "[]((signal(2) == 3) -> signal(0) > 22.5)",
        "[]((signal(2) == 3) -> signal(0) > 25)",
        "[]((signal(2) == 3) -> signal(0) > 27.5)",
        "[]((signal(2) == 3) -> signal(0) > 30)"
    ),
    inputMapper,
    outputMapperReader
)
val signalLength = 30
val properties = AdaptiveSTLList(stlList, signalLength)

// Constants for the GA-based equivalence testing
val maxTest = 50000
val populationSize = 200
val crossoverProb = 0.5
val mutationProb = 0.01

// Load the automatic transmission model. This automatically closes MATLAB
SimulinkSUL(initScript, paramNames, signalStep, simulinkSimulationStep).use { autoTransSUL ->
    // Configure and run the verifier
    val verifier = NumericSULVerifier(autoTransSUL, signalStep, properties, mapper)
    // Timeout must be set before adding equivalence testing
    verifier.setTimeout(5 * 60) // 5 minutes
    verifier.addGAEQOracleAll(
        signalLength,
        maxTest,
        GASelectionKind.Tournament,
        populationSize,
        crossoverProb,
        mutationProb
    )
    val result = verifier.run()

    // Print the result and stats (shared helpers)
    printResults(verifier, result)
    printStats(verifier)
}
