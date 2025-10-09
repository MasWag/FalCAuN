#!/usr/bin/env kscript

// Import the constants for AutoTrans
@file:Import("./AutoTrans.kt")
// This script depends on FalCAuN-core and FalCAuN-matlab
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT", "net.maswag.falcaun:FalCAuN-matlab:1.0-SNAPSHOT")
// We assume that the MATLAB_HOME environment variable is set
@file:KotlinOptions("-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64")

import ch.qos.logback.classic.Level
import ch.qos.logback.classic.Logger
import net.automatalib.modelchecker.ltsmin.AbstractLTSmin
import net.automatalib.modelchecker.ltsmin.LTSminVersion
import net.maswag.falcaun.*
import org.slf4j.LoggerFactory
import kotlin.streams.toList

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

val overallStart = System.currentTimeMillis()

// Define the input and output mappers
val throttleValues = listOf(0.0, 100.0)
val brakeValues = listOf(0.0, 325.0)
val inputMapper = InputMapperReader.make(listOf(throttleValues, brakeValues))
val velocityValues = listOf(40.0, 50.0, 60.0, 90.0, null)
val accelerationValues = listOf(null)
val gearValues = listOf(null)
val outputMapperReader = OutputMapperReader(listOf(velocityValues, accelerationValues, gearValues))
outputMapperReader.parse()
val signalMapper = ExtendedSignalMapper()


// Define the STL properties
val stlFactory = STLFactory()
val stlList = listOf(
    // "[] (signal(0) < 90)"
    // "([]_[0, 26] (signal(0) < 90)) || ([]_[28, 28] (signal(0) > 50))", // ok
    // "([]_[0, 26] (signal(0) < 90)) || ([]_[28, 28] (signal(0) > 60))",
    "[] ((signal(0) < 40)  -> ([]_[0,8] (signal(0) < 60)))",
    "[] ((signal(0) < 50)  -> ([]_[0,8] (signal(0) < 60)))",
    "[] ((signal(0) < 40)  -> ([]_[0,10] (signal(0) < 60)))",
    "[] ((signal(0) < 50)  -> ([]_[0,10] (signal(0) < 60)))",
    "[] ((signal(0) < 40)  -> ([]_[0,8] (signal(0) < 90)))",
    "[] ((signal(0) < 50)  -> ([]_[0,8] (signal(0) < 90)))",
    "[] ((signal(0) < 40)  -> ([]_[0,10] (signal(0) < 90)))",
    "[] ((signal(0) < 50)  -> ([]_[0,10] (signal(0) < 90)))"
).stream().map { stlString ->
    stlFactory.parse(
        stlString,
        inputMapper,
        outputMapperReader.outputMapper,
        outputMapperReader.largest
    )
}.toList()
val signalLength = 30
val properties = AdaptiveSTLList(stlList, signalLength)

var mapper : NumericSULMapper? = null
if (args[0] == "original"){
    mapper =
        NumericSULMapper(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper)
} else if (args[0] == "abstract"){
    mapper = NumericSULMapperWithSGA(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper, stlList,false)
} else if (args[0] == "partial") {
    mapper = NumericSULMapperWithSGA(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper, stlList, true)
}

// Constants for the GA-based equivalence testing
val maxTest = 50000
val populationSize = 200
val crossoverProb = 0.5
val mutationProb = 0.01

var checkingStart = System.currentTimeMillis()

// Load the automatic transmission model. This automatically closes MATLAB
SimulinkSUL(initScript, paramNames, signalStep, simulinkSimulationStep).use { autoTransSUL ->
    // Configure and run the verifier
    val verifier = NumericSULVerifier(autoTransSUL, signalStep, properties, mapper)
    checkingStart = System.currentTimeMillis()
    // Timeout must be set before adding equivalence testing
    verifier.setTimeout(20 * 60) // 20 minutes
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
        }
    }
    println("Execution time for simulation: ${verifier.simulationTimeSecond} [sec]")
    println("Number of simulations: ${verifier.simulinkCount}")
    println("Number of simulations for equivalence testing: ${verifier.simulinkCountForEqTest}")
}

val overallEnd = System.currentTimeMillis()

println("Initialization Time: ${(checkingStart - overallStart)/1000.0}")
println("Learning and Checking Time: ${(overallEnd - checkingStart)/1000.0}")
println("Overall Time: ${(overallEnd - overallStart)/1000.0}")