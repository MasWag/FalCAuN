#!/usr/bin/env kscript

// Import the constants for AutoTrans
@file:Import("./AutoTrans.kt")
// This script depends on FalCAuN-core and FalCAuN-matlab
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT", "net.maswag.falcaun:FalCAuN-matlab:1.0-SNAPSHOT")
// We assume that the MATLAB_HOME environment variable is set
@file:KotlinOptions("-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64")

import net.maswag.falcaun.*
import kotlin.streams.toList

// Define the input and output mappers
val throttleValues = listOf(0.0, 100.0)
val brakeValues = listOf(0.0, 325.0)
val inputMapper = InputMapperReader.make(listOf(throttleValues, brakeValues))
val velocityValues = listOf(20.0, 22.5, 25.0, 27.5, 30.0, null)
val accelerationValues = listOf(null)
val gearValues = listOf(2.0, 3.0, null)
val outputMapperReader = OutputMapperReader(listOf(velocityValues, accelerationValues, gearValues))
outputMapperReader.parse()
val signalMapper = SimpleSignalMapper()
val mapper =
    NumericSULMapper(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper)

// Define the STL properties
val stlFactory = STLFactory()
val stlList = listOf(
    "[]((signal(2) == 3) -> signal(0) > 20)",
    "[]((signal(2) == 3) -> signal(0) > 22.5)",
    "[]((signal(2) == 3) -> signal(0) > 25)",
    "[]((signal(2) == 3) -> signal(0) > 27.5)",
    "[]((signal(2) == 3) -> signal(0) > 30)"
).stream().map { stlString ->
    stlFactory.parse(
        stlString,
        inputMapper,
        outputMapperReader.outputMapper,
        outputMapperReader.largest
    )
}.toList()
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
        ArgParser.GASelectionKind.Tournament,
        populationSize,
        crossoverProb,
        mutationProb
    )
    val result = verifier.run()

    // Print the result
    if (result) {
        println("The property is likely satisfied")
    } else {
        println("The property is falsified")
        for (i in 0 until verifier.cexProperty.size) {
            println("${verifier.cexProperty[i]} is falsified by the following counterexample)")
            println("cex concrete input: ${verifier.cexConcreteInput[i]}")
            println("cex abstract input: ${verifier.cexAbstractInput[i]}")
            println("cex output: ${verifier.cexOutput[i]}")
        }
    }
}
