#!/usr/bin/env kscript

// This script depends on FalCAuN-core
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT")

import ch.qos.logback.classic.Level
import ch.qos.logback.classic.Logger
import de.learnlib.driver.simulator.MealySimulatorSUL
import de.learnlib.oracle.membership.SULOracle
import net.automatalib.alphabet.Alphabets
import net.automatalib.automaton.transducer.CompactMealy
import net.automatalib.modelchecker.ltsmin.AbstractLTSmin
import net.automatalib.modelchecker.ltsmin.LTSminVersion
import net.automatalib.util.automaton.builder.AutomatonBuilders
import net.automatalib.visualization.Visualization
import net.maswag.falcaun.*
import net.maswag.falcaun.parser.LTLFactory
import org.slf4j.LoggerFactory
import java.util.*

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

// Define the target Mealy machine
// 1. input alphabet contains strings "a" and "b"
val sigma = Alphabets.fromList(listOf("a", "b"))
// 2. output alphabet contains strings "p" and "q"
val gamma = Alphabets.fromList(listOf("p", "q"))
// 3. create Mealy machine
// @formatter:off
val target: CompactMealy<String, String> = AutomatonBuilders.newMealy<String, String>(sigma)
    .withInitial("q0")
    .from("q0")
        .on("a").withOutput("p").to("q1")
        .on("b").withOutput("q").to("q2")
    .from("q1")
        .on("a").withOutput("q").to("q0")
        .on("b").withOutput("p").to("q3")
    .from("q2")
        .on("a").withOutput("p").to("q3")
        .on("b").withOutput("p").to("q0")
    .from("q3")
        .on("a").withOutput("q").to("q2")
        .on("b").withOutput("q").to("q1")
    .create()
// @formatter:on

// This shows the target Mealy machine in a new window. The script is blocked until the window is closed.
Visualization.visualize(target.transitionGraphView(sigma))

// Define LTL properties
val ltlFactory = LTLFactory()
val ltlList =
    listOf(
        "[] (output == p -> X (output == q))", // This does not hold
        "[] ((input == a && output == p && (X input == a)) -> (X output == q))", // This holds
    ).map { stlString ->
        ltlFactory.parse(stlString)
    }.toList()
val signalLength = 10 // We believe that the traces of length 10 are enough to verify/falsify the properties
val properties = AdaptiveSTLList(ltlList, signalLength)

// Define the SUL and oracle
val sul = MealySimulatorSUL(target)
val oracle = SULOracle(sul)
properties.setMemOracle(oracle)

// Configure and run the verifier
val verifier = BlackBoxVerifier(oracle, sul, properties, sigma)
// Timeout must be set before adding equivalence testing
verifier.setTimeout(5 * 60) // 5 minutes
verifier.addRandomWordEQOracle(
    1, // The minimum length of the random word
    10, // The maximum length of the random word
    1000, // The maximum number of tests
    Random(),
    1,
)
val result = verifier.run()

// Print the result
if (result) {
    println("All the properties are likely satisfied")
} else {
    println("Some properties are falsified")
    for (i in 0 until verifier.cexProperty.size) {
        println("${verifier.cexProperty[i]} is falsified by the following counterexample:")
        println("cex concrete input: ${verifier.cexInput[i]}")
        println("cex output: ${verifier.cexOutput[i]}")
    }
}
