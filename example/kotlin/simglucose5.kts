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

// Reduce verbose logs
surpressesLog()

// Define the input and output mappers
val ignoreValues = listOf(null)
val mealSizeValues = listOf(0.0, 50.0)
val inputMapper = InputMapperReader.make(listOf(mealSizeValues))
// The 10th-percentile and 90th-percentile thresholds
val tenthBg = 66.2
val ninetiethBg = 189.2
val bgValues = listOf(tenthBg, ninetiethBg, null)
val minbgValues = listOf(189.2, null)
val maxbgValues = listOf(66.2, null)
val insulinValues = listOf(0.5, null)
val deltaBgValues = listOf(null)
val outputMapperReader = OutputMapperReader(listOf(bgValues, insulinValues, minbgValues, maxbgValues, deltaBgValues, deltaBgValues))
val signalMapper = ExtendedSignalMapper()
val mapper = NumericSULMapper(inputMapper, outputMapperReader, signalMapper)

// Define the STL properties. The properties are taken from the following paper.
// - Young, William, et al. "DAMON: A data authenticity monitoring
//   system for diabetes management." 2018 IEEE/ACM Third International
//   Conference on Internet-of-Things Design and Implementation
//   (IoTDI). IEEE, 2018.
val stlList = parseStlList(
    listOf(
        // BG should not stay below 10th-percentile threshold for more than 120 minutes.
        "G($bg > $tenthBg || F_[0, ${(120 / stepDuration).toInt()}] $max_bg > $tenthBg)",
        // BG should not stay above 90th-percentile threshold for more than 120 minutes.
        "G($bg < $ninetiethBg || F_[0, ${(120 / stepDuration).toInt()}] $min_bg < $ninetiethBg)",
        // BG should not stay above 90th-percentile threshold for more than 150 minutes after an insuline injection.
        "G($bg < $ninetiethBg || $insulin < 0.5 || F_[0, ${(150 / stepDuration).toInt()}] $min_bg < $ninetiethBg)",
    ),
    inputMapper,
    outputMapperReader
)
val signalLength = 30 // 30 * 30 mins
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
    verifier.setTimeout(5 * 60 * 8) // 40 minutes
    verifier.addCornerCaseEQOracle(signalLength, signalLength / 2);
    verifier.addGAEQOracleAll(
        signalLength,
        maxTest,
        ArgParser.GASelectionKind.Tournament,
        populationSize,
        crossoverProb,
        mutationProb
    )
    val result = verifier.run()

    // Print the result and stats (shared helpers)
    printResults(verifier, result)
    printStats(verifier)
}
