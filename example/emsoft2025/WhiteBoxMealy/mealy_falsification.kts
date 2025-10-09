#!/usr/bin/env kscript

// This script depends on FalCAuN-core and FalCAuN-matlab
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT")
// @file:DependsOn("org.jgrapht:jgrapht-core:1.5.2", "org.jgrapht:jgrapht-io:1.5.2")
// @file:DependsOn("org.antlr:antlr4-maven-plugin:4.12.0", "org.antlr:antlr4-runtime:4.12.0")
// We assume that the MATLAB_HOME environment variable is set
@file:KotlinOptions("-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64")

import ch.qos.logback.classic.Level
import ch.qos.logback.classic.Logger
import de.learnlib.driver.simulator.MealySimulatorSUL
import de.learnlib.filter.statistic.oracle.MealyCounterOracle;
import de.learnlib.oracle.membership.SULOracle
import de.learnlib.mapper.MappedSUL
import de.learnlib.sul.SUL
import net.automatalib.alphabet.Alphabets
import net.automatalib.automaton.transducer.CompactMealy
import net.automatalib.modelchecker.ltsmin.AbstractLTSmin
import net.automatalib.modelchecker.ltsmin.LTSminVersion
import net.automatalib.util.automaton.builder.AutomatonBuilders
import net.automatalib.visualization.Visualization
import net.maswag.falcaun.*
import org.slf4j.LoggerFactory
import java.util.*
import java.io.*

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

val timeBeforeInit = System.currentTimeMillis()

// Read the target Mealy machine from dotfile
val file_index = args[1]
var wrapper = DotMealyWrapper("dotfiles/m" + file_index)
// 1. input alphabet contains strings "a" and "b"
val sigma = wrapper.sigma
// 2. output alphabet contains strings "p" and "q"
val gamma = wrapper.gamma

// Define LTL properties
val ltlFactory = LTLFactory()
val file = File("./ltl_FalCAuN/m" + file_index + "_ltl_FalCAuN.txt")
var formulaList = file.readLines().take(args[2].toInt())
val ltlList =
    formulaList.map { stlString ->
        ltlFactory.parse(stlString)
    }.toList()
val signalLength = 50 // We believe that the traces of length 50 are enough to verify/falsify the properties
val properties = AdaptiveSTLList(ltlList, signalLength)

// Define the SUL and oracle
var mapper : Map<String, String>? = null
if (args[0] == "original") {
    mapper = HashMap<String, String>()
} else if (args[0] == "partial") {
    mapper = SGAMapper(ltlList, sigma, gamma, true).outputMapper
} else if (args[0] == "abstract") {
    mapper = SGAMapper(ltlList, sigma, gamma, false).outputMapper
}
val target = wrapper.createMealy(mapper)

var sul : SUL<String, String> = MealySimulatorSUL(target)

val memOracle = SULOracle(sul)
val counterOracle = MealyCounterOracle(memOracle)
properties.setMemOracle(counterOracle)

// Configure and run the verifier
val verifier = BlackBoxVerifier(counterOracle, sul, properties, sigma)
// Timeout must be set before adding equivalence testing
verifier.setTimeout(10 * 60) // 5 minutes
val eqOracle = WhiteBoxEqOracle(target)
verifier.addEqOracle(eqOracle)

val timeBeforeFalsification = System.currentTimeMillis()

val result = verifier.run()

val timeAfterFalsification = System.currentTimeMillis()

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

println("# of ltl formulae: ${ltlList.size}")
println("# of falsified ltl formulae: ${verifier.cexProperty.size}")
println("# of MQ: ${counterOracle.getQueryCounter().getCount()}")
println("Time for initialize: ${(timeBeforeFalsification - timeBeforeInit)}")
println("Time for falsification: ${(timeAfterFalsification - timeBeforeFalsification)}")