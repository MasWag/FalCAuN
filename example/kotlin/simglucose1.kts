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
// surpressesLog()

// Define the input and output mappers
val ignoreValues = listOf(null)
val mealSizeValues = listOf(0.0, 50.0)
val inputMapper = InputMapperReader.make(listOf(mealSizeValues))
val bgValues = listOf(90.0, null)
val insulinValues = listOf(0.5, null)
val deltaBgValues = listOf(-5.0, 3.0, null)
val outputMapperReader = OutputMapperReader(listOf(ignoreValues, insulinValues, ignoreValues, bgValues, deltaBgValues, deltaBgValues))
val signalMapper = ExtendedSignalMapper()
val mapper = NumericSULMapper(inputMapper, outputMapperReader, signalMapper)

// Define the STL properties. The properties are taken from the following paper.
// - Young, William, et al. "DAMON: A data authenticity monitoring
//   system for diabetes management." 2018 IEEE/ACM Third International
//   Conference on Internet-of-Things Design and Implementation
//   (IoTDI). IEEE, 2018.
val stlList = parseStlList(
    listOf(
        // If BG is not low, insulin administration accompanies the diet
        // We use || instead of -> because specification strengthening does not support -> yet
        "G($max_bg < 90.0 || $mealSize != 50 || $insulin > 0.5)",
        // The change in BG is between -5 and 3.
        "G($min_delta_bg > -5.0 && $max_delta_bg < 3.0)",
        // The change in BG is between -5 and 3 if the meal is not given too much
        // "(($mealSize == 50.0 && X ($mealSize == 50.0))) R ($min_delta_bg > -5.0 && $max_delta_bg < 3.0)",
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
