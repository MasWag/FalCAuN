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
import net.maswag.falcaun.VerificationResult
import net.maswag.falcaun.parser.STLFactory
import net.maswag.falcaun.parser.TemporalLogic
import org.slf4j.LoggerFactory

/**
 * Adjust logger levels to reduce verbose output.
 *
 * Sets several FalCAuN/LTSmin-related loggers to `INFO` to suppress
 * debug/trace messages during runs of the examples.
 */
fun surpressesLog() {
    var updaterLogger = LoggerFactory.getLogger(AbstractAdaptiveSTLUpdater::class.java) as Logger
    updaterLogger.level = Level.INFO
    var updateListLogger = LoggerFactory.getLogger(AdaptiveSTLList::class.java) as Logger
    updateListLogger.level = Level.INFO
    var ltsminVersionLogger = LoggerFactory.getLogger(LTSminVersion::class.java) as Logger
    ltsminVersionLogger.level = Level.INFO
    var abstractLtsminLogger = LoggerFactory.getLogger(AbstractLTSmin::class.java) as Logger
    abstractLtsminLogger.level = Level.INFO
    var eqSearchProblemLogger = LoggerFactory.getLogger(EQSearchProblem::class.java) as Logger
    eqSearchProblemLogger.level = Level.INFO
    var simulinkSteadyStateGeneticAlgorithmLogger = LoggerFactory.getLogger(EQSteadyStateGeneticAlgorithm::class.java) as Logger
    simulinkSteadyStateGeneticAlgorithmLogger.level = Level.INFO
}

/**
 * Parse a list of STL specifications into evaluable costs.
 *
 * @param stlList List of STL formulas as strings.
 * @param inputMapper Mapping from abstract input symbols to concrete values per step.
 * @param outputMapperReader Provider for output mapping and signal bounds used by parsing.
 * @return Parsed list of `STLCost` instances corresponding to the input formulas.
 */
fun parseStlList(
    stlList: List<String>,
    inputMapper: List<Map<Char, Double>>,
    outputMapperReader: OutputMapperReader,
): List<TemporalLogic.STLCost> {
    val stlFactory = STLFactory()
    val outputMapper = outputMapperReader.getOutputMapper()
    val largest = outputMapperReader.getLargest()
    return stlList
        .stream()
        .map { stlString ->
            stlFactory.parse(
                stlString,
                inputMapper,
                outputMapper,
                largest,
            )
        }.toList()
}

/**
 * Print verification result and counterexamples (if any) to stdout.
 *
 * Prints each property falsified by a counterexample confirmed by the SUL along with
 * its concrete/abstract inputs and the observed outputs.
 * If no counterexample is found, the result is inconclusive: it does not prove the properties.
 *
 * @param verifier The `NumericSULVerifier` used to construct the concrete inputs.
 * @param result The result of `verifier.run()`.
 */
fun printResults(
    verifier: NumericSULVerifier,
    result: VerificationResult<List<Double>>,
) {
    val counterexamples = result.confirmedCounterexamples()
    if (counterexamples.isEmpty()) {
        println("No counterexample is found (termination reason: ${result.reason()})")
    } else {
        if (result.allTargetsFalsified()) {
            println("All the properties are falsified")
        } else {
            println("Some properties are falsified")
        }
        for (cex in counterexamples) {
            println("${cex.property()} is falsified by the following counterexample")
            println("cex concrete input: ${verifier.concreteInput(cex)}")
            println("cex abstract input: ${cex.abstractInput()}")
            println("cex output: ${cex.sutOutput()}")
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
fun printStats(verifier: NumericSULVerifier) {
    println("Execution time for simulation: ${verifier.simulationTimeSecond} [sec]")
    println("Number of simulations: ${verifier.sutExecutionCount}")
    println("Number of simulations for equivalence testing: ${verifier.eqSutExecutionCount}")
}
