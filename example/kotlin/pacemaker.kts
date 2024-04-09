#!/usr/bin/env kscript
/*****h* kotlin/pacemaker
 *  NAME
 *   pacemaker.kts
 *  DESCRIPTION
 *   Script to falsify the "pacemaker" formula by FalCAuN
 *  AUTHOR
 *   Masaki Waga
 *  HISTORY
 *    - 2024/04/09: initial version
 *  COPYRIGHT
 *   Copyright (c) 2024 Masaki Waga
 *   Released under the MIT license
 *   https://opensource.org/licenses/mit-license.php
 *
 *  PORTABILITY
 *   This script asuses the following:
 *   - FalCAuN is installed, for example, by mvn install.
 *   - The environment variable MATLAB_HOME is set to the root directory of MATLAB, e.g., /Applications/MATLAB_R2024a.app/ or /usr/local/MATLAB/R2024a.
 *
 *  USAGE
 *   ./pacemaker.kts
 *  NOTES
 *   By default, this script runs FalCAuN for 50 times. When you want to run for a different interval, specify the range by the first and the second arguments.
 *
 ********/

package net.maswag

// This script depends on FalCAuN-core and FalCAuN-matlab
@file:DependsOn("net.maswag:FalCAuN-core:1.0-SNAPSHOT", "net.maswag:FalCAuN-matlab:1.0-SNAPSHOT")
// We assume that the MATLAB_HOME environment variable is set
@file:KotlinOptions("-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64")

import net.maswag.*
import kotlin.streams.toList

// Define the input and output mappers
val lriValues = listOf(50.0, 90.0)
val inputMapper = InputMapperReader.make(listOf(lriValues))
val periodValues = listOf(null)
val lrlValues = listOf(null)
val paceCountValues = listOf(8.0, 15.0, null)
val outputMapperReader = OutputMapperReader(listOf(periodValues, lrlValues, paceCountValues))
outputMapperReader.parse()
val signalMapper = SignalMapper()
val mapper =
    NumericSULMapper(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper)

// Define the output signal names
val period = "signal(0)"
val LRL = "signal(1)"
val paceCount = "signal(2)"

// Define the STL properties
val stlFactory = STLFactory()
val stlList = listOf(
    stlFactory.parse(
        "(alw_[5,5] $LRL > 0) -> ((alw_[0,5] $paceCount < 15) && (ev_[0,5] $paceCount > 8))",
        inputMapper,
        outputMapperReader.outputMapper,
        outputMapperReader.largest
    )
)
println(stlList.get(0).toAbstractString())
val signalLength = 6
val properties = AdaptiveSTLList(stlList, signalLength)

val initScript = """
%% Init Script for the pacemaker model

%% Load the pacemaker model
mdl = 'Model1_Scenario1_Correct'
load_system(mdl);

% The initial pacing conditions in the Simulink model are used.
init_cond = []; 
"""
val paramNames = listOf("LRI")
val signalStep = 2.0
val simulinkSimulationStep = 0.0025

// Constants for the GA-based equivalence testing
val maxTest = 1000
val populationSize = 50
val crossoverProb = 0.9
val mutationProb = 0.01

// Load the automatic transmission model. This automatically closes MATLAB
SimulinkSUL(initScript, paramNames, signalStep, simulinkSimulationStep).use { pacemakerSUL ->
    // Configure and run the verifier
    val verifier = NumericSULVerifier(pacemakerSUL, signalStep, properties, mapper)
    // Timeout must be set before adding equivalence testing
    verifier.setTimeout(10 * 60) // 10 minutes
    verifier.addGAEQOracleAll(
        signalLength,
        maxTest,
        ArgParser.GASelectionKind.Tournament,
        populationSize,
        crossoverProb,
        mutationProb
    )
    val result = verifier.run()

    // Print the result
    if (result) {
        println("The property is likely satisfied")
    } else {
        println("The property is falsified")
        for (i in 0 until verifier.cexProperty.size) {
            println("${verifier.cexProperty[i]} is falsified by the following counterexample)")
            println("cex concrete input: ${verifier.cexConcreteInput[i]}")
            println("cex abstract input: ${verifier.cexAbstractInput[i]}")
            println("cex output: ${verifier.cexOutput[i]}")
        }
    }
}
