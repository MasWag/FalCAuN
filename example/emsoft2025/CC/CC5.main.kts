#!/usr/bin/env kscript
/*****h* CC/CC3
 *  NAME
 *   CC3.main.kts
 *  DESCRIPTION
 *   Script to falsify the chasing cars benchmark against the CC3 formula by FalCAuN
 *  AUTHOR
 *   Masaki Waga
 *  HISTORY
 *    - 2024/04/26: Initial version
 *  COPYRIGHT
 *   Copyright (c) 2024 Masaki Waga
 *   Released under the MIT license
 *   https://opensource.org/licenses/mit-license.php
 *
 *  PORTABILITY
 *   This script assumes the following:
 *   - FalCAuN is installed, for example, by mvn install.
 *   - The environment variable MATLAB_HOME is set to the root directory of MATLAB, e.g., /Applications/MATLAB_R2024a.app/ or /usr/local/MATLAB/R2024a.
 *
 *  USAGE
 *   ./CC3.main.kts
 *
 ********/

@file:Import("./Cars.kt") // Import the constants for Chasing Cars

import net.maswag.falcaun.*
import java.io.BufferedReader
import java.io.StringReader
import kotlin.streams.toList

logger.info("This is the script to falsify the chasing car benchmark against the CC3 formula by FalCAuN")

val fullTimer = TimeMeasure()
fullTimer.start()

// The number of repetitions of the experiment
var experimentSize = 1
if (args.size > 0) {
    experimentSize = args[1].toInt()
    logger.info("The experiment is executed for $experimentSize times")
} else {
    logger.info("The number of repetitions of the experiment is not specified. We use the default repetition size $experimentSize")
}

// Define the output mapper
val ignoredValues = listOf(null)
val y2y1Values = listOf(9.0, null)
val y5y4Values = listOf(9.0, null)
val outputMapperReader =
    OutputMapperReader(listOf(ignoredValues, ignoredValues, ignoredValues, ignoredValues, ignoredValues, y2y1Values, y5y4Values))
outputMapperReader.parse()
val mapperString = listOf("previous_max($y2 - $y1)", "previous_max($y5 - $y4)").joinToString("\n")
val signalMapper: ExtendedSignalMapper = ExtendedSignalMapper.parse(BufferedReader(StringReader(mapperString)))
assert(signalMapper.size() == 2)

// Define the pseudo signal names
// Pseudo signals representing the maximum and minimum values between sampling points
// These signals exclude the begin time and include the end time
val diffy2y1 = "signal(5)"
val diffy5y4 = "signal(6)"

// Define the STL properties
val stlFactory = STLFactory()
val stlList =
    listOf(
        "(alw_[0,${scaleDuration(10)}] (ev_[0,${scaleDuration(7)}]((alw_[0,${scaleDuration(5)}] $diffy2y1 > 9) -> (alw_[5,${scaleDuration(20)}] $diffy5y4 > 9))))",
    ).stream().map { stlString ->
        stlFactory.parse(
            stlString,
            inputMapper,
            outputMapperReader.outputMapper,
            outputMapperReader.largest,
        )
    }.toList()
// We need to add by one because the first sample is at time 0
val signalLength = (100 / signalStep).toInt() + 1
val properties = AdaptiveSTLList(stlList, signalLength)

var mapper : NumericSULMapper? = null
if (args[0] == "original"){
    mapper =
        NumericSULMapper(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper)
} else if (args[0] == "abstract"){
    mapper = NumericSULMapperWithSGA(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper, stlList, false)
} else if (args[0] == "partial") {
    mapper = NumericSULMapperWithSGA(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper, stlList, true)
}

// Load the chasing car model. This automatically closes MATLAB
SimulinkSUL(initScript, paramNames, signalStep, simulinkSimulationStep).use { sul ->
    // Create a list to store the results
    val results = mutableListOf<ExperimentSummary>()
    // Repeat the following experiment for the specified number of times
    for (i in 0 until experimentSize) {
        // Since SUL counts the number of simulations and the execution time, we need to clear it before each experiment
        sul.clear()
        logger.info("Experiment ${i + 1} / $experimentSize")
        // Configure and run the verifier
        val verifier = NumericSULVerifier(sul, signalStep, properties, mapper)
        // Timeout must be set before adding equivalence testing
        verifier.setTimeout(10 * 60) // 10 minutes
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
        // Run the experiment
        var result = runExperiment(verifier, "CC", "CC3")
        results.add(result)
    }
    FileOutputStream("result-CC3.csv").apply { writeCsv(results) }
    logger.info("The results are written to result-CC3.csv")
}

fullTimer.stop()
logger.info("Total time: ${fullTimer.getSecond()} [sec]")