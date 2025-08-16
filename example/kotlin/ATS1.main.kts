#!/usr/bin/env kscript
/*****h* kotlin/ATS1
 *  NAME
 *   ATS1.main.kts
 *  DESCRIPTION
 *   Script to falsify the automatic transmission benchmark against the S1 formula by FalCAuN
 *  AUTHOR
 *   Masaki Waga
 *  HISTORY
 *    - 2024/04/20: Use ExtendedSignalMapper
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
 *   ./ATS1.main.kts
 *
 ********/

// Import the common utilities
@file:Import("./Common.kt")
// Import the constants for AutoTrans
@file:Import("./AutoTrans.kt")
// This script depends on FalCAuN-core and FalCAuN-matlab
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT", "net.maswag.falcaun:FalCAuN-matlab:1.0-SNAPSHOT")
// We assume that the MATLAB_HOME environment variable is set
@file:KotlinOptions("-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64")

import net.automatalib.modelchecker.ltsmin.AbstractLTSmin
import net.automatalib.modelchecker.ltsmin.LTSminVersion
import net.maswag.falcaun.*
import kotlin.streams.toList

// The following suppresses the debug log

// Define the input and output mappers
val throttleValues = listOf(0.0, 100.0)
val brakeValues = listOf(0.0, 325.0)
val inputMapper = InputMapperReader.make(listOf(throttleValues, brakeValues))
val velocityValues = listOf(20.0, 40.0, 60.0, 80.0, 100.0, 120.0, null)
val accelerationValues = listOf(null)
val gearValues = listOf(null)
val outputMapperReader = OutputMapperReader(listOf(velocityValues, accelerationValues, gearValues))
val signalMapper = ExtendedSignalMapper()
val mapper = NumericSULMapper(inputMapper, outputMapperReader, signalMapper)

// Define the STL properties
val stlList = parseStlList(listOf(
                               "[] (signal(0) < 120)",
                               "[] (signal(0) < 100)",
                               "[] (signal(0) < 80)",
                               "[] (signal(0) < 60)",
                               "[] (signal(0) < 40)",
                               "[] (signal(0) < 20)"
                           ),
                           inputMapper,
                           outputMapperReader)
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

    // Print the result
    printResults(verifier, result)
    printStats(verifier)
}
