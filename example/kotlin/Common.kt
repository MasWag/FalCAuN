import org.slf4j.LoggerFactory
import ch.qos.logback.classic.Level
import ch.qos.logback.classic.Logger
import net.automatalib.modelchecker.ltsmin.AbstractLTSmin
import net.automatalib.modelchecker.ltsmin.LTSminVersion
import net.maswag.falcaun.AbstractAdaptiveSTLUpdater
import net.maswag.falcaun.AdaptiveSTLList
import net.maswag.falcaun.EQSearchProblem
import net.maswag.falcaun.EQSteadyStateGeneticAlgorithm
import net.maswag.falcaun.NumericSULVerifier
import net.maswag.falcaun.OutputMapperReader
import net.maswag.falcaun.parser.STLFactory
import net.maswag.falcaun.parser.TemporalLogic

/**
 * Adjust logger levels to reduce verbose output.
 *
 * Sets several FalCAuN/LTSmin-related loggers to `INFO` to suppress
 * debug/trace messages during runs of the examples.
 */
fun surpressesLog(): Unit {
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
}

/**
 * Parse a list of STL specifications into evaluable costs.
 *
 * @param stlList List of STL formulas as strings.
 * @param inputMapper Mapping from abstract input symbols to concrete values per step.
 * @param outputMapperReader Provider for output mapping and signal bounds used by parsing.
 * @return Parsed list of `STLCost` instances corresponding to the input formulas.
 */
fun parseStlList(stlList: List<String>, inputMapper: List<Map<Char, Double>>, outputMapperReader: OutputMapperReader) : List<TemporalLogic.STLCost> {
    val stlFactory = STLFactory()
    val outputMapper = outputMapperReader.getOutputMapper()
    val largest = outputMapperReader.getLargest()
    return stlList.stream().map {stlString ->
        stlFactory.parse(
            stlString,
            inputMapper,
            outputMapper,
            largest
        )
    }.toList()
}

/**
 * Print verification result and counterexamples (if any) to stdout.
 *
 * When `result` is false, prints each falsified property along with
 * its concrete/abstract inputs and observed outputs from the verifier.
 *
 * @param verifier The `NumericSULVerifier` that holds counterexample data.
 * @param result Overall verification outcome; true if all properties held.
 */
fun printResults(verifier: NumericSULVerifier, result: Boolean): Unit {
    if (result) {
        println("All the properties are likely satisfied")
    } else {
        if (verifier.properties.size() == verifier.cexProperty.size) {
            println("All the properties are falsified")
        } else {
            println("Some properties are falsified")
        }
        for (i in 0 until verifier.cexProperty.size) {
            println("${verifier.cexProperty[i]} is falsified by the following counterexample")
            println("cex concrete input: ${verifier.cexConcreteInput[i]}")
            println("cex abstract input: ${verifier.cexAbstractInput[i]}")
            println("cex output: ${verifier.cexOutput[i]}")
        }
    }
}

/**
 * Print execution statistics to stdout.
 *
 * Includes total simulation time and counts of total simulations and
 * simulations performed during equivalence testing.
 *
 * @param verifier The `NumericSULVerifier` source of statistics.
 */
fun printStats(verifier: NumericSULVerifier): Unit {
    println("Execution time for simulation: ${verifier.simulationTimeSecond} [sec]")
    println("Number of simulations: ${verifier.simulinkCount}")
    println("Number of simulations for equivalence testing: ${verifier.simulinkCountForEqTest}")
}
