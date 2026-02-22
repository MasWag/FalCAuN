#!/usr/bin/env kscript
// Define the dependent libraries
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT")
@file:DependsOn("net.maswag.falcaun:FalCAuN-examples:1.0-SNAPSHOT")

// Import the common utilities
@file:Import("./Common.kt")

// Import the libraries
import de.learnlib.oracle.membership.SULOracle
import java.util.Random
import kotlin.streams.toList
import net.maswag.falcaun.*
import net.maswag.falcaun.example.*
import net.maswag.falcaun.parser.*

// Reduce verbose logs
surpressesLog()

// Define the tested properties
val ltlFactory = LTLFactory()
val properties = StaticSTLList(
    listOf(
        "G (output == LongPress -> X (output == None))",
        "G (output == DoubleClick -> X (output == None))",
        "G (output == SingleClick -> X (output == None))"
    ).map { ltlString ->
        ltlFactory.parse(ltlString)
    }.toList())
println("We try ${properties}")

// Load the buggy version of ButtonDetector model from FalCAuN-examples.
ButtonDetectorBuggy(100).use { rawSul ->
    val sul = ButtonDetectorMapper(rawSul)
    val memOracle = SULOracle(sul)
    properties.setMemOracle(memOracle)

    val verifier = BlackBoxVerifier(memOracle, sul, properties,
                                    ButtonDetectorMapper.getInputAlphabet())
    verifier.addRandomWordEQOracle(10, 20, 1000, Random(), 1)
    val falsified = !verifier.run()
    if (falsified) {
        println("Some of the properties were falsified.")
        for (i in 0 until verifier.cexProperty.size) {
            println("${verifier.cexProperty[i]} is falsified.")
            println("Input: ${verifier.cexInput[i]}")
            println("Output: ${verifier.cexOutput[i]}")
        }
    } else {
        println("No property was falsified.")
    }
    // Disabled for CI/headless runs because visualization requires a GUI.
    // verifier.visualizeLearnedMealy()
}
