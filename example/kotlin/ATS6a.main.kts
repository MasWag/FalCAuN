#!/usr/bin/env kscript

// Import the constants for AutoTrans
@file:Import("./AutoTrans.kt")
// This script depends on FalCAuN-core and FalCAuN-matlab
@file:DependsOn("net.maswag:FalCAuN-core:1.0-SNAPSHOT", "net.maswag:FalCAuN-matlab:1.0-SNAPSHOT")
// We assume that the MATLAB_HOME environment variable is set
@file:KotlinOptions("-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64")

import net.maswag.*
import kotlin.streams.toList
import java.io.BufferedReader
import java.io.StringReader

// Define the input and output mappers
val throttleValues = listOf(0.0, 50.0, 100.0)
val brakeValues = listOf(0.0, 325.0)
val inputMapper = InputMapperReader.make(listOf(throttleValues, brakeValues))
val velocityValues = listOf(35.0, null)
val accelerationValues = listOf(3000.0, null)
val ignoreValues = listOf(null)
val gearValues = listOf(null)
//val outputMapperReader = OutputMapperReader(listOf(velocityValues, accelerationValues, gearValues, velocityValues, accelerationValues))
val outputMapperReader = OutputMapperReader(listOf(ignoreValues, ignoreValues, gearValues, velocityValues, accelerationValues))
outputMapperReader.parse()
val mapperString = listOf("previous_max_output(0)", "previous_max_output(1)").joinToString("\n")
val signalMapper: ExtendedSignalMapper = ExtendedSignalMapper.parse(BufferedReader(StringReader(mapperString)))
val mapper =
    NumericSULMapper(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper)

// Define the output signal names
val velocity = "signal(0)"
val rotation = "signal(1)"
val gear = "signal(2)"
// Pseudo signals representing the maximum and minimum values between sampling points
// These signals exclude the begin time and include the end time
val prevMaxVelocity = "output(3)"
val prevMaxRotation = "output(4)"

// Define the STL properties
val stlFactory = STLFactory()
signalStep = 1.0
//val stlGRotationLt3000 = "$rotation < 3000.0 && []_[0, ${(30 / signalStep).toInt()}] ($prevMaxRotation < 3000.0)"
val stlGRotationLt3000 = "[]_[0, ${(30 / signalStep).toInt()}] ($prevMaxRotation < 3000.0)"
val stlNotGRotationLt3000 = "<>_[0, ${(30 / signalStep).toInt()}] ($prevMaxRotation > 3000.0)"
//val STLGVelocityLt35 = "$velocity < 35.0 && []_[0,${(4 / signalStep).toInt()}] ($prevMaxVelocity < 35.0)"
val STLGVelocityLt35 = "[]_[0,${(4 / signalStep).toInt()}] ($prevMaxVelocity < 35.0)"
val stlList = listOf(
    //"($stlGRotationLt3000) -> ($STLGVelocityLt35)",
    // We use || instead of -> because specification strengthening does not support -> yet
    // "(!($stlGRotationLt3000)) || ($STLGVelocityLt35)",
    // Similarly, we use <>! instead of ![]
    "($stlNotGRotationLt3000) || ($STLGVelocityLt35)",
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
val maxTest = 500000
val populationSize = 200
val crossoverProb = 0.5
val mutationProb = 0.01

// Load the automatic transmission model. This automatically closes MATLAB
SimulinkSUL(initScript, paramNames, signalStep, simulinkSimulationStep).use { autoTransSUL ->
    // Configure and run the verifier
    val verifier = NumericSULVerifier(autoTransSUL, signalStep, properties, mapper)
    // Timeout must be set before adding equivalence testing
    verifier.setTimeout(50 * 60) // 50 minutes
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
