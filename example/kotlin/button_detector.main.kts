#!/usr/bin/env kscript
// Define the dependent libraries
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT")
@file:DependsOn("net.maswag.falcaun:FalCAuN-examples:1.0-SNAPSHOT")

// Import the common utilities
@file:Import("./Common.kt")

// Import the libraries

import de.learnlib.oracle.membership.SULOracle
import net.maswag.falcaun.temporal.*
import net.maswag.falcaun.verification.*
import net.maswag.falcaun.example.*
import java.util.Random
import kotlin.streams.toList

// Reduce verbose logs
surpressesLog()

// Define the tested properties
val ltlFactory = LTLFactory()
val properties =
    StaticSTLList(
        listOf(
            "G (output == LongPress -> X (output == None))",
            "G (output == DoubleClick -> X (output == None))",
            "G (output == SingleClick -> X (output == None))",
        ).map { ltlString ->
            ltlFactory.parse(ltlString)
        }.toList(),
    )
println("We try $properties")

// Load the buggy version of ButtonDetector model from FalCAuN-examples.
ButtonDetectorBuggy(100).use { rawSul ->
    val sul = ButtonDetectorMapper(rawSul)
    val memOracle = SULOracle(sul)
    properties.setMemOracle(memOracle)

    val verifier =
        BlackBoxVerifier(
            memOracle,
            sul,
            properties,
            ButtonDetectorMapper.getInputAlphabet(),
        )
    verifier.addRandomWordEQOracle(10, 20, 1000, Random(), 1)
    val counterexamples = verifier.run().confirmedCounterexamples()
    if (counterexamples.isNotEmpty()) {
        println("Some of the properties were falsified.")
        for (cex in counterexamples) {
            println("${cex.property()} is falsified.")
            println("Input: ${cex.abstractInput()}")
            println("Output: ${cex.sutOutput()}")
        }
    } else {
        println("No property was falsified.")
    }
    // Disabled for CI/headless runs because visualization requires a GUI.
    // verifier.visualizeLearnedMealy()
}
