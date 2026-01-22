#!/usr/bin/env kscript

// This script depends on FalCAuN-core
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT")

import ch.qos.logback.classic.Level
import ch.qos.logback.classic.Logger
import de.learnlib.acex.AcexAnalyzers
import de.learnlib.algorithm.ttt.mealy.TTTLearnerMealy
import de.learnlib.driver.simulator.MealySimulatorSUL
import de.learnlib.oracle.membership.SULOracle
import de.learnlib.oracle.equivalence.MealySimulatorEQOracle
import de.learnlib.filter.statistic.oracle.MealyCounterOracle
import de.learnlib.sul.SUL
import net.automatalib.modelchecker.ltsmin.AbstractLTSmin
import net.automatalib.modelchecker.ltsmin.LTSminVersion
import net.automatalib.util.automaton.minimizer.HopcroftMinimizer
import net.maswag.falcaun.*
import net.maswag.falcaun.parser.LTLFactory
import org.slf4j.LoggerFactory
import java.util.*
import java.io.*
import kotlin.system.exitProcess

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

if (args.size < 2 || (args[0] != "original" && args.size < 3)) {
    System.err.println("Usage: learning.kts <original|partial|abstract> <mealy_index> [ltl_count]")
    exitProcess(1)
}

val timeBeforeInit = System.currentTimeMillis()

// Read the target Mealy machine from dotfile
val file_index = args[1]
var wrapper = DotMealyWrapper("dotfiles/m" + file_index)
// 1. input alphabet contains strings "a" and "b"
val sigma = wrapper.sigma
// 2. output alphabet contains strings "p" and "q"
val gamma = wrapper.gamma
// 3. create Mealy machine

var mapper : Map<String, String>? = null
if (args[0] == "original") {
    mapper = HashMap<String, String>()
} else {
    // Define LTL properties
    val ltlFactory = LTLFactory()
    val file = File("ltl_FalCAuN/m" + file_index + "_ltl_FalCAuN.txt")
    var formulaList = file.readLines().take(args[2].toInt())
    val ltlList =
        formulaList.map { stlString ->
            ltlFactory.parse(stlString)
        }.toList()
    val signalLength = 50 // We believe that the traces of length 50 are enough to verify/falsify the properties
    if (args[0] == "partial") {
        mapper = SGAMapper(ltlList, sigma, gamma, true).outputMapper
    } else if (args[0] == "abstract") {
        mapper = SGAMapper(ltlList, sigma, gamma, false).outputMapper
    }
}

// Define the SUL and oracle
val target = wrapper.createMealy(mapper)
val minimizedTarget = HopcroftMinimizer.minimizeMealy(target, sigma)

var sul : SUL<String, String> = MealySimulatorSUL(target)

val memOracle = SULOracle(sul)
val counterOracle = MealyCounterOracle(memOracle)

val learner = TTTLearnerMealy<String, String>(sigma, counterOracle, AcexAnalyzers.LINEAR_FWD)
val eqOracle = MealySimulatorEQOracle(target)

val timeBeforeLearning = System.currentTimeMillis()

var round = 1
learner.startLearning()
var hypothesisMealy = learner.getHypothesisModel()
var cexQuery = eqOracle.findCounterExample(hypothesisMealy, sigma)

while (cexQuery != null) {
    round++
    learner.refineHypothesis(cexQuery)
    hypothesisMealy = learner.getHypothesisModel()
    cexQuery = eqOracle.findCounterExample(hypothesisMealy, sigma)
}

val timeAfterLearning = System.currentTimeMillis()

println("Actual # of states: ${minimizedTarget.size()}")
println("# of states: ${hypothesisMealy.size()}")
println("# of membership queries: ${counterOracle.getQueryCounter().getCount() - round}")
println("# of symbols: ${counterOracle.getSymbolCounter().getCount()}")
println("# of equivalence queries(rounds): ${round}")
println("Time for initialize: ${timeBeforeLearning - timeBeforeInit}")
println("Time for learning: ${timeAfterLearning - timeBeforeLearning}")


// Visualization.visualize(learnedMealy.transitionGraphView(sigma))
