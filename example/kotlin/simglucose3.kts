#!/usr/bin/env kscript

// Import shared helpers
@file:Import("./Common.kt")
@file:Import("./Simglucose.kt")
// This script depends on FalCAuN-core and FalCAuN-python
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT", "net.maswag.falcaun:FalCAuN-python:1.0-SNAPSHOT")
// And requires JEP library
// Below is an example path to the JEP library when using pyenv and python 3.10.15
//@file:KotlinOptions("-Djava.library.path=$PYENV_ROOT/versions/3.10.15/lib/python3.10/site-packages/jep")

import net.maswag.falcaun.*
// Reduce verbose logs via common helper
surpressesLog()

// Define the input and output mappers
val ignoreValues = listOf(null)
val mealSizeValues = listOf(0.0, 50.0)
val inputMapper = InputMapperReader.make(listOf(mealSizeValues))
val bgValues = listOf(55.0, 180.0, 240.0)
val insulinValues = listOf(0.5)
val outputMapperReader = OutputMapperReader(listOf(bgValues, insulinValues, bgValues, ignoreValues, ignoreValues, ignoreValues))
val signalMapper = ExtendedSignalMapper()
val mapper = NumericSULMapper(inputMapper, outputMapperReader, signalMapper)

// Define the STL properties
val stlList = parseStlList(
    listOf(
        // BG does not go below 55
        "G($min_bg > 55.0)",
        // Does not exceed the upper 10% for more than 30 minutes
        "(input(0) == 50.0 && X (input(0) == 50.0)) R ($bg > 180.0 -> X ($min_bg < 180.0))",
        // Does not exceed the upper 10% for more than 30 minutes after insulin administration
        "(input(0) == 50.0 && X (input(0) == 50.0)) R ($insulin > 0.5 -> X ($min_bg < 180.0))",
        // Hyperglycemia does not last longer than 180 minutes
        "(input(0) == 50.0 && X (input(0) == 50.0)) R ! []_[0, ${(180.0 / stepDuration).toInt()}] ($min_bg > 240.0)",
    ),
    inputMapper,
    outputMapperReader
)
val signalLength = 48 //3*10 * 24 mins
val properties = AdaptiveSTLList(stlList, signalLength)

// Constants for the GA-based equivalence testing
val maxTest = 50000
val populationSize = 200
val crossoverProb = 0.5
val mutationProb = 0.01

// Load the simglucose model implemented by python
makeSimglucoseSUL().use { sul ->
    // Configure and run the verifier
    val verifier = NumericSULVerifier(sul, signalStep, properties, mapper)
    // Timeout must be set before adding equivalence testing
    verifier.setTimeout(5 * 60 * 8) // 5 minutes
    verifier.addCornerCaseEQOracle(signalLength, signalLength / 2);
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
