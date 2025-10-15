#!/usr/bin/env kscript

// This script depends on FalCAuN-core
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT")

import ch.qos.logback.classic.Level
import ch.qos.logback.classic.Logger
import de.learnlib.acex.AcexAnalyzers;
import de.learnlib.algorithm.ttt.mealy.TTTLearnerMealy;
import de.learnlib.driver.simulator.MealySimulatorSUL
import de.learnlib.filter.cache.mealy.MealyCacheOracle
import de.learnlib.filter.cache.mealy.MealyCaches
import de.learnlib.oracle.membership.SULOracle
import de.learnlib.oracle.equivalence.MealyRandomWordsEQOracle;
import de.learnlib.filter.statistic.oracle.MealyCounterOracle;
import de.learnlib.mapper.MappedSUL;
import de.learnlib.query.DefaultQuery
import de.learnlib.sul.SUL;
import de.learnlib.util.Experiment;
import net.automatalib.alphabet.Alphabets
import net.automatalib.automaton.transducer.CompactMealy
import net.automatalib.modelchecker.ltsmin.AbstractLTSmin
import net.automatalib.modelchecker.ltsmin.LTSminVersion
import net.automatalib.util.automaton.builder.AutomatonBuilders
import net.automatalib.util.automaton.equivalence.DeterministicEquivalenceTest
import net.automatalib.util.automaton.minimizer.hopcroft.HopcroftMinimization
import net.automatalib.visualization.Visualization
import net.automatalib.word.Word


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

var sul : SUL<String, String> = MealySimulatorSUL(target)

val memOracle = SULOracle(sul)
val counterOracle = MealyCounterOracle(memOracle)

val learner = TTTLearnerMealy<String, String>(sigma, counterOracle, AcexAnalyzers.LINEAR_FWD)

val timeBeforeLearning = System.currentTimeMillis()

var round = 1
learner.startLearning()
var hypothesisMealy = learner.getHypothesisModel()
var cexInput = DeterministicEquivalenceTest.findSeparatingWord(target, hypothesisMealy, sigma)

while (cexInput != null) {
    round++
    val cexOutput = memOracle.answerQuery(cexInput)
    val refinementQuery = DefaultQuery<String, Word<String>>(Word.epsilon(), cexInput, cexOutput)
    learner.refineHypothesis(refinementQuery)
    hypothesisMealy = learner.getHypothesisModel()
    cexInput = DeterministicEquivalenceTest.findSeparatingWord(target, hypothesisMealy, sigma)
}

val timeAfterLearning = System.currentTimeMillis()

val minimizedTarget = HopcroftMinimization.minimizeMealy(target, sigma)

println("Actual # of states: ${minimizedTarget.size()}")
println("# of states: ${hypothesisMealy.size()}")
println("# of membership queries: ${counterOracle.getQueryCounter().getCount() - round}")
println("# of symbols: ${counterOracle.getSymbolCounter().getCount()}")
println("# of equivalence queries(rounds): ${round}")
println("Time for initialize: ${timeBeforeLearning - timeBeforeInit}")
println("Time for learning: ${timeAfterLearning - timeBeforeLearning}")


// Visualization.visualize(learnedMealy.transitionGraphView(sigma))
