#!/usr/bin/env kscript

// This script depends on FalCAuN-core and FalCAuN-examples
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT")
@file:DependsOn("net.maswag.falcaun:FalCAuN-examples:1.0-SNAPSHOT")
// We use kotlin-logging for logging
@file:DependsOn("io.github.oshai:kotlin-logging-jvm:5.1.0")

import ch.qos.logback.classic.Level
import ch.qos.logback.classic.Logger
import de.learnlib.driver.simulator.MealySimulatorSUL
import de.learnlib.oracle.membership.SULOracle
import io.github.oshai.kotlinlogging.KotlinLogging
import net.automatalib.alphabet.impl.Alphabets
import net.automatalib.automaton.transducer.impl.CompactMealy
import net.automatalib.modelchecker.ltsmin.AbstractLTSmin
import net.automatalib.modelchecker.ltsmin.LTSminVersion
import net.automatalib.util.automaton.builder.AutomatonBuilders
import net.automatalib.visualization.Visualization
import net.maswag.falcaun.*
import org.slf4j.LoggerFactory
import java.util.*
import java.io.BufferedReader
import java.io.StringReader
import kotlin.streams.toList

// The following surprises the debug log
var loggerUpdater = LoggerFactory.getLogger(AbstractAdaptiveSTLUpdater::class.java) as Logger
loggerUpdater.level = Level.INFO
var loggerUpdateList = LoggerFactory.getLogger(AdaptiveSTLList::class.java) as Logger
loggerUpdateList.level = Level.INFO
var loggerLTSminVersion = LoggerFactory.getLogger(LTSminVersion::class.java) as Logger
loggerLTSminVersion.level = Level.INFO
var loggerAbstractLTSmin = LoggerFactory.getLogger(AbstractLTSmin::class.java) as Logger
loggerAbstractLTSmin.level = Level.INFO
var loggerEQSearchProblem = LoggerFactory.getLogger(EQSearchProblem::class.java) as Logger
loggerEQSearchProblem.level = Level.INFO
var loggerSimulinkSteadyStateGeneticAlgorithm = LoggerFactory.getLogger(EQSteadyStateGeneticAlgorithm::class.java) as Logger
loggerSimulinkSteadyStateGeneticAlgorithm.level = Level.INFO

// Declare the logger
val logger = KotlinLogging.logger {}

logger.info("This is the script to falsify the bouncing ball benchmark with FalCAuN")

// Define the input mapper
var signalStep = 1.0
val windValues = listOf(0.0, 2.5)
val inputMapper = InputMapperReader.make(listOf(windValues))

// Define the output signal names
val position = "signal(0)"
val velocity = "signal(1)"

// Define the output mapper
val positionValues = listOf(45.0, null)
val velocityValues = listOf(null)
val outputMapperReader = OutputMapperReader(listOf(positionValues, velocityValues, positionValues))
outputMapperReader.parse()
val mapperString = listOf("previous_max_output(0)").joinToString("\n")
val signalMapper: ExtendedSignalMapper = ExtendedSignalMapper.parse(BufferedReader(StringReader(mapperString)))
assert(signalMapper.size() == 1)
val mapper =
    NumericSULMapper(inputMapper, outputMapperReader.largest, outputMapperReader.outputMapper, signalMapper)

// Define the pseudo signal names
val prevMaxPosition = "output(2)"

// Define the STL properties
val stlFactory = STLFactory()
val stlList =
    listOf(
        "(ev_[0,${(10 / signalStep).toInt()}] alw $prevMaxPosition < 45)",
    ).stream().map { stlString ->
        stlFactory.parse(
            stlString,
            inputMapper,
            outputMapperReader.outputMapper,
            outputMapperReader.largest,
        )
    }.toList()
// We need to add by one because the first sample is at time 0
val signalLength = (20 / signalStep).toInt() + 1


// Define the SUL and oracle
val sul = BouncingBallSUL()
val oracle = SULOracle(sul)

// Constants for the GA-based equivalence testing
val maxTest = 50000
val populationSize = 50
val crossoverProb = 0.9
val mutationProb = 0.01

// Configure and run the verifier
// val verifier = BlackBoxVerifier(oracle, sul, properties, sigma)
val properties = AdaptiveSTLList(stlList, signalLength)
// properties.setMemOracle(oracle)
val verifier = NumericSULVerifier(sul, signalStep, properties, mapper)
// Timeout must be set before adding equivalence testing
verifier.setTimeout(5 * 60) // 5 minutes
// We first try the corner cases
verifier.addCornerCaseEQOracle(signalLength, signalLength / 2)
// Then, search with GA
verifier.addGAEQOracleAll(
    signalLength,
    maxTest,
    ArgParser.GASelectionKind.Tournament,
    populationSize,
    crossoverProb,
    mutationProb,
)

// verifier.addRandomWordEQOracle(
//     1, // The minimum length of the random word
//     10, // The maximum length of the random word
//     1000, // The maximum number of tests
//     Random(),
//     1,
// )
val result = verifier.run()

// Print the result
if (result) {
    println("All the properties are likely satisfied")
} else {
    println("Some properties are falsified")
    for (i in 0 until verifier.cexProperty.size) {
        println("${verifier.cexProperty[i]} is falsified by the following counterexample:")
        println("cex concrete input: ${verifier.cexConcreteInput[i]}")
        println("cex output: ${verifier.cexOutput[i]}")
    }
}
println("The number of simulations: ${verifier.simulinkCount}")
