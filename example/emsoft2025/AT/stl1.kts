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
import net.maswag.falcaun.abstraction.*
import net.maswag.falcaun.oracle.*
import net.maswag.falcaun.signal.*
import net.maswag.falcaun.temporal.*
import net.maswag.falcaun.verification.*
import net.maswag.falcaun.temporal.STLFactory
import net.maswag.falcaun.simulink.SimulinkSUL
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
val velocityValues = listOf(110.0, 115.0, 120.0, null)
val accelerationValues = listOf(null)
val gearValues = listOf(null)
val outputMapperReader = OutputMapperReader(listOf(velocityValues, accelerationValues, gearValues))
outputMapperReader.parse()
val signalMapper = ExtendedSignalMapper()

// Define the STL properties
val stlFactory = STLFactory()
val stlList = listOf(
    "[] (signal(0) < 110)",
    "[] (signal(0) < 115)",
    "[] (signal(0) < 120)"
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

val mapperMode = args.getOrNull(0) ?: "original"
var mapper : SignalDiscretizer? = null
if (mapperMode == "original"){
    mapper =
        NumericSULMapper(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper)
} else if (mapperMode == "abstract"){
    mapper = NumericSULMapperWithSGA(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper, stlList, false)
    properties.setMapper((mapper as NumericSULMapperWithSGA).getPostOutputMapper().get())
} else if (mapperMode == "partial") {
    mapper = NumericSULMapperWithSGA(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper, stlList, true)
    properties.setMapper((mapper as NumericSULMapperWithSGA).getPostOutputMapper().get())
}

// Constants for the GA-based equivalence testing
val maxTest = 50000
val populationSize = 200
val crossoverProb = 0.5
val mutationProb = 0.01

val checkingStart = System.currentTimeMillis()

// Load the automatic transmission model. This automatically closes MATLAB
SimulinkSUL(initScript, paramNames, signalStep, simulinkSimulationStep).use { autoTransSUL ->
    // Configure and run the verifier
    val verifier = NumericSULVerifier(autoTransSUL, signalStep, properties, mapper)
    // Timeout must be set before adding equivalence testing
    verifier.setTimeout(20 * 60) // 20 minutes
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
    val cexs = result.confirmedCounterexamples()

    // Print the result
    if (cexs.isEmpty()) {
        println("No counterexample is found (termination reason: ${result.reason()})")
    } else {
        for (i in 0 until cexs.size) {
            println("${cexs[i].property()} is falsified by the following counterexample")
            println("cex concrete input: ${verifier.concreteInput(cexs[i])}")
            println("cex abstract input: ${cexs[i].abstractInput()}")
            println("cex output: ${cexs[i].sutOutput()}")
        }
    }
    println("Execution time for simulation: ${verifier.simulationTimeSecond} [sec]")
    println("Number of simulations: ${verifier.sutExecutionCount}")
    println("Number of simulations for equivalence testing: ${verifier.eqEvaluationCount}")
}

val overallEnd = System.currentTimeMillis()

println("Initialization Time: ${(checkingStart - overallStart)/1000.0}")
println("Learning and Checking Time: ${(overallEnd - checkingStart)/1000.0}")
println("Overall Time: ${(overallEnd - overallStart)/1000.0}")
