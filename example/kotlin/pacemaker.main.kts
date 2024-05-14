#!/usr/bin/env kscript
/*****h* kotlin/pacemaker
 *  NAME
 *   pacemaker.main.kts
 *  DESCRIPTION
 *   Script to falsify the "pacemaker" formula by FalCAuN
 *  AUTHOR
 *   Masaki Waga
 *  HISTORY
 *    - 2024/04/09: initial version
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
 *   ./pacemaker.main.kts
 *  NOTES
 *   By default, this script runs FalCAuN for 50 times. When you want to run for a different interval, specify the range by the first and the second arguments.
 *
 ********/

// This script depends on FalCAuN-core and FalCAuN-matlab
@file:DependsOn("net.maswag:FalCAuN-core:1.0-SNAPSHOT")
@file:DependsOn("net.maswag:FalCAuN-matlab:1.0-SNAPSHOT")
// We assume that the MATLAB_HOME environment variable is set
@file:KotlinOptions("-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64")

import net.maswag.*
import java.io.BufferedReader
import java.io.StringReader

// Set up the pacemaker model
val initScript = """
%% Init Script for the pacemaker model

%% Load the pacemaker model
mdl = 'Model1_Scenario1_Correct';
load_system(mdl);

% The initial pacing conditions in the Simulink model are used.
init_cond = []; 
"""
val paramNames = listOf("LRI")
val signalStep = 0.5
val simulinkSimulationStep = 0.0025

// Define the input and output mappers
val lriValues = listOf(50.0, 60.0, 70.0, 80.0, 90.0)
val inputMapper = InputMapperReader.make(listOf(lriValues))
val ignoreValue = listOf(null)
val paceCountValues = listOf(7.0, 16.0, null)
val outputMapperReader = OutputMapperReader(listOf(ignoreValue, ignoreValue, paceCountValues, paceCountValues, ignoreValue))
outputMapperReader.parse()
val mapperString = listOf("previous_max_output(2)", "previous_min_output(2)").joinToString("\n")
val signalMapper: ExtendedSignalMapper = ExtendedSignalMapper.parse(BufferedReader(StringReader(mapperString)))
assert(signalMapper.size() == 2)
val mapper =
    NumericSULMapper(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper)

// Define the output signal names
val period = "signal(0)"
val LRL = "signal(1)"
val paceCount = "signal(2)"
// Pseudo signals representing the maximum and minimum values between sampling points
// These signals exclude the begin time and include the end time
val prevMaxPaceCount = "output(3)"
val prevMinPaceCount = "output(4)" // We do not use the minimum values show as an example

// Define the STL properties
val stlFactory = STLFactory()
// Signal must be long enough
val stlSignalLength = "alw_[${(10 / signalStep).toInt()},${(10 / signalStep).toInt()}] $LRL > 0"
val stlGPaceCountLt15 = "($paceCount < 16.0 && alw_[0,${(10 / signalStep).toInt()}] $prevMaxPaceCount < 16.0)"
val stlFPaceCountGt8 = "($paceCount > 7.0 || ev_[0,${(10 / signalStep).toInt()}] $prevMaxPaceCount > 7.0)"
val stlList = listOf(
    stlFactory.parse(
        "(!($stlSignalLength)) || ($stlGPaceCountLt15 && $stlFPaceCountGt8)",
        inputMapper,
        outputMapperReader.outputMapper,
        outputMapperReader.largest
    )
)
println(stlList.get(0).toAbstractString())
val signalLength = (12 / signalStep).toInt()
val properties = AdaptiveSTLList(stlList, signalLength)

// Constants for the GA-based equivalence testing
val maxTest = 10000
val populationSize = 50
val crossoverProb = 0.9
val mutationProb = 0.01

// Load the automatic transmission model. This automatically closes MATLAB
SimulinkSUL(initScript, paramNames, signalStep, simulinkSimulationStep).use { pacemakerSUL ->
    // Configure and run the verifier
    val verifier = NumericSULVerifier(pacemakerSUL, signalStep, properties, mapper)
    // Timeout must be set before adding equivalence testing
    verifier.setTimeout(10 * 60) // 10 minutes
    // We first try equivalence testing based on corner case inputs
    verifier.addCornerCaseEQOracle(signalLength, signalLength / 2)
    // Then, we use genetic algorithm
    verifier.addGAEQOracleAll(
        signalLength,
        maxTest,
        ArgParser.GASelectionKind.Tournament,
        populationSize,
        crossoverProb,
        mutationProb
    )
    //verifier.addWpMethodEQOracle(6)
    val result = verifier.run()

    // Print the result
    if (result) {
        println("The property is likely satisfied")
    } else {
        for (i in 0 until verifier.cexProperty.size) {
            println("${verifier.cexProperty[i]} is falsified by the following counterexample")
            println("cex concrete input: ${verifier.cexConcreteInput[i]}")
            println("cex abstract input: ${verifier.cexAbstractInput[i]}")
            println("cex output: ${verifier.cexOutput[i]}")
        }
    }
    println("Execution time for simulation: ${verifier.simulationTimeSecond} [sec]")
    println("Number of simulations: ${verifier.simulinkCount}")
    println("Number of simulations for equivalence testing: ${verifier.simulinkCountForEqTest}")
}
