#!/usr/bin/env kscript
// Define the dependent libraries
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT")
@file:DependsOn("net.maswag.falcaun:FalCAuN-examples:1.0-SNAPSHOT")

// Import the common utilities
@file:Import("./Common.kt")

// Import the libraries

import de.learnlib.oracle.membership.SULOracle
import net.maswag.falcaun.*
import net.maswag.falcaun.example.*
import net.maswag.falcaun.parser.*
import java.util.Random
import kotlin.streams.toList

// Reduce verbose logs
surpressesLog()

// Define the input mapper
val windValues = listOf(0.0, 2.5)
val inputMapper = InputMapper.make(listOf(windValues))

// Define the output mapper
val positionValues = listOf(45.0, null)
val velocityValues = listOf(null)
val outputMapper =
    OutputMapper(listOf(positionValues, velocityValues, positionValues))
val adapter = SignalAdapter(inputMapper, outputMapper)

val signalStep = BouncingBallSUL.DEFAULT_SIMULATION_STEP // = 1.0

// Define the signal deriver
// output(0) represents the ball position.
val deriverString = listOf("previous_max(output(0))")
val deriver = SignalDeriver.parse(deriverString)
val mapper = adapter.preCompose(deriver)

// Define the STL properties
val stlFactory = STLFactory()
val stlFormula =
    stlFactory.parse(
        // output(2) corresponds to previous_max(output(0))
        "(F_[0,${(10 / signalStep).toInt()}] G output(2) < 45)",
        inputMapper,
        outputMapper,
    )

// Add one because the first sample is at time 0
val signalLength = (10 / signalStep).toInt() + 1

val properties = AdaptiveSTLList(listOf(stlFormula), signalLength)

println("We try $properties")

// Load the BouncingBall model from FalCAuN-examples.
BouncingBallSUL().use { sul ->
    val oracle = SULOracle(sul)

    // Constants for the GA-based equivalence testing
    val maxTest = 50000
    val populationSize = 50
    val crossoverProb = 0.9
    val mutationProb = 0.01

    val verifier = NumericSULVerifier(sul, 1.0, properties, mapper)

    // Timeout must be set before adding equivalence testing
    verifier.setTimeout(5 * 60) // 5 minutes
    // We first try the corner cases
    verifier.addCornerCaseEQOracle(signalLength, signalLength / 2)
    // Then, search with GA
    verifier.addGAEQOracleAll(
        signalLength,
        maxTest,
        GASelectionKind.Tournament,
        populationSize,
        crossoverProb,
        mutationProb,
    )

    val result = verifier.run()
    if (result) {
        println("All the properties are likely satisfied")
    } else {
        if (verifier.properties.size() == verifier.cexProperty.size) {
            println("All the properties are falsified")
        } else {
            println("Some properties are falsified")
        }
        for (i in 0 until verifier.cexProperty.size) {
            println("${verifier.cexProperty[i]} is falsified.")
            println("cex concrete input: ${verifier.cexConcreteInput[i]}")
            println("cex abstract input: ${verifier.cexAbstractInput[i]}")
            println("cex output: ${verifier.cexOutput[i]}")
        }
    }
    // Disabled for CI/headless runs because visualization requires a GUI.
    // verifier.visualizeLearnedMealy()
}
