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

var signalStep = 1.0
val initScript = "./simglucose_example.py"

// This script depends on FalCAuN-core and FalCAuN-matlab
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT", "net.maswag.falcaun:FalCAuN-python:1.0-SNAPSHOT")
// We assume that the MATLAB_HOME environment variable is set
@file:KotlinOptions("-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64:/home/sugina/.pyenv/versions/3.10.15/lib/python3.10/site-packages/jep")

import ch.qos.logback.classic.Level
import ch.qos.logback.classic.Logger
import net.automatalib.modelchecker.ltsmin.AbstractLTSmin
import net.automatalib.modelchecker.ltsmin.LTSminVersion
import net.maswag.falcaun.*
import org.slf4j.LoggerFactory
import kotlin.streams.toList
import net.automatalib.word.Word;

// The following surprises the debug log
var updaterLogger = LoggerFactory.getLogger(AbstractAdaptiveSTLUpdater::class.java) as Logger
updaterLogger.level = Level.INFO
var updateListLogger = LoggerFactory.getLogger(AdaptiveSTLList::class.java) as Logger
updateListLogger.level = Level.INFO
var LTSminVersionLogger = LoggerFactory.getLogger(LTSminVersion::class.java) as Logger
LTSminVersionLogger.level = Level.INFO
var AbstractLTSminLogger = LoggerFactory.getLogger(AbstractLTSmin::class.java) as Logger
AbstractLTSminLogger.level = Level.INFO
var EQSearchProblemLogger = LoggerFactory.getLogger(EQSearchProblem::class.java) as Logger
EQSearchProblemLogger.level = Level.INFO
var SimulinkSteadyStateGeneticAlgorithmLogger = LoggerFactory.getLogger(EQSteadyStateGeneticAlgorithm::class.java) as Logger
SimulinkSteadyStateGeneticAlgorithmLogger.level = Level.INFO

// Define the input and output mappers
val mealSizeValues = listOf(0.0, 80.0) // <20?
val inputMapper = InputMapperReader.make(listOf(mealSizeValues))
val bgValues = listOf(55.0, 70.0, 400.0) // <300?
val insulinValues = listOf(0.5) //listOf(0.3, 0.6) // <3?
val outputMapperReader = OutputMapperReader(listOf(bgValues, insulinValues, bgValues))
outputMapperReader.parse()
val signalMapper = ExtendedSignalMapper()
val mapper =
    NumericSULMapper(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper)

val bg = "signal(0)"
val insulin = "signal(1)"
val max_bg = "signal(2)"
val alpha = 10

// Define the STL properties
val stlFactory = STLFactory()
val stlList = listOf(
    //"[] ($bg > 55)",
    //"[] ($bg > 55 && $bg < 400.0)",
    "[] ($bg < 70.0 -> X ($max_bg > 70.0))", //下位10%以下を 30 分以上取らない
    "! <> []_[0,5] ($max_bg < 70)", //低血糖状態が150分以上続かない
    "($bg < 70) -> ($insulin < 0.5)", //低血糖状態で inslin を打たない
    //"! <> X X X X X X ($bg > 240)", //高血糖状態が180分以上続かない
).stream().map { stlString ->
    stlFactory.parse(
        stlString,
        inputMapper,
        outputMapperReader.outputMapper,
        outputMapperReader.largest
    )
}.toList()
val signalLength = 24 //3*10 * 24 mins
val properties = AdaptiveSTLList(stlList, signalLength)

// Constants for the GA-based equivalence testing
val maxTest = 50000
val populationSize = 200
val crossoverProb = 0.5
val mutationProb = 0.01

// Load the automatic transmission model. This automatically closes MATLAB
PythonNumericSUL(initScript, signalStep).use { autoTransSUL ->
    // Configure and run the verifier
    val verifier = NumericSULVerifier(autoTransSUL, signalStep, properties, mapper)
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

    // Print the result
    if (result) {
        println("The property is likely satisfied")
    } else {
        for (i in 0 until verifier.cexProperty.size) {
            println("${verifier.cexProperty[i]} is falsified by the following counterexample")
            println("cex concrete input: ${verifier.cexConcreteInput[i]}")
            println("cex abstract input: ${verifier.cexAbstractInput[i]}")
            println("cex output: ${verifier.cexOutput[i]}")


            var rawOutput = mutableListOf<List<List<Double>>>()
            val dim = mutableListOf<List<Double>>()
            for (j in 0 until verifier.cexConcreteInput[i].size()) {
                dim.add(verifier.cexConcreteInput[i].get(j))
            }
            val inputWord = Word.fromList(dim)
            val resultWord = autoTransSUL.execute(inputWord).getOutputSignal()
            rawOutput.add(resultWord.asList())
            println("cex concrete output: ${rawOutput}")
        }
    }
    println("Execution time for simulation: ${verifier.simulationTimeSecond} [sec]")
    println("Number of simulations: ${verifier.simulinkCount}")
    println("Number of simulations for equivalence testing: ${verifier.simulinkCountForEqTest}")
}
