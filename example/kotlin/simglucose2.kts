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
val bgValues = listOf(55.0, 70.0, 400.0)
val insulinValues = listOf(0.5)
val outputMapperReader = OutputMapperReader(listOf(bgValues, insulinValues, ignoreValues, bgValues, ignoreValues, ignoreValues))
val signalMapper = ExtendedSignalMapper()
val mapper = NumericSULMapper(inputMapper, outputMapperReader, signalMapper)

// Define the STL properties. The properties are taken from the following paper.
// - Young, William, et al. "DAMON: A data authenticity monitoring
//   system for diabetes management." 2018 IEEE/ACM Third International
//   Conference on Internet-of-Things Design and Implementation
//   (IoTDI). IEEE, 2018.
val stlList = parseStlList(
    listOf(
        // BG does not go above 180
        // "G($max_bg < 180.0)",
        // BG does not go below 70
        // "G($min_bg > 70.0)",
        // // BG does not go above 400
        "G($max_bg < 400.0)",
        // BG does not go above 400 if the meal is not given too much
        // "($mealSize == 50.0 && X ($mealSize == 50.0)) R ($max_bg < 400.0)",
        // Does not fall below the lower 10% for more than 30 minutes
        "G($bg < 70.0 -> X ($max_bg > 70.0))",
        // Does not fall below the lower 10% for more than 30 minutes if the meal is not given too much
        // "($mealSize == 50.0 && X ($mealSize == 50.0)) R ($bg < 70.0 -> X ($max_bg > 70.0))",
        // Hypoglycemia does not last longer than 150 minutes
        "G(F_[0, ${(150.0 / stepDuration).toInt()}] ($max_bg > 70.0))",
        // Hypoglycemia does not last longer than 150 minutes if the meal is not given too much
        // "(input(0) == 50.0 && X (input(0) == 50.0)) R ! []_[0,$alpha] ($max_bg < 70.0)",
        // Does not administer insulin when hypoglycemia
        "G($bg < 70.0 -> $insulin < 0.5)",
        // Does not administer insulin when hypoglycemia if the meal is not given too much
        // "(input(0) == 50.0 && X (input(0) == 50.0)) R ($bg < 70.0 -> $insulin < 0.5)",
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
