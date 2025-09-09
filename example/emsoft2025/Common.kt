/*****h* FalCAuN-ARCH-COMP/Common
 *  NAME
 *   Common.kt
 *  DESCRIPTION
 *   The common configuration for running FalCAuN via kscript.
 *  AUTHOR
 *   Masaki Waga
 *  HISTORY
 *    - 2024/04/26: Initial version
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
 ********/

// The scripts depends on FalCAuN-core and FalCAuN-matlab
@file:DependsOn("net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT", "net.maswag.falcaun:FalCAuN-matlab:1.0-SNAPSHOT")
// We use kotlin-logging for logging
@file:DependsOn("io.github.oshai:kotlin-logging-jvm:5.1.0")
// We assume that the MATLAB_HOME environment variable is set
@file:KotlinOptions("-Djava.library.path=$MATLAB_HOME/bin/maca64/:$MATLAB_HOME/bin/maci64:$MATLAB_HOME/bin/glnxa64")

import ch.qos.logback.classic.Level
import ch.qos.logback.classic.Logger
import org.slf4j.LoggerFactory
import net.automatalib.modelchecker.ltsmin.AbstractLTSmin
import net.automatalib.modelchecker.ltsmin.LTSminVersion
import io.github.oshai.kotlinlogging.KotlinLogging
import java.io.OutputStream
import java.io.FileOutputStream

// Constants for the GA-based equivalence testing
val maxTest = 50000
val populationSize = 50
val crossoverProb = 0.9
val mutationProb = 0.01

// The following suppresses the debug log
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
var MealyFixedSetLogger = LoggerFactory.getLogger(MealyFixedSetEQOracle::class.java) as Logger
MealyFixedSetLogger.level = Level.DEBUG

// Declare the logger
val logger = KotlinLogging.logger {}

// Declare the data class for the summary of the experimental results
data class ExperimentSummary(
    val system: String,
    val property: String,
    val totalSimulations: Int,
    val totalTime: Double,
    val simulationsForEqTest: Int,
    val simulationTime: Double,
    val falsified: String,
    val input: String
)

/**
 * Write the summary of experiments to a CSV file.
 *
 * @param summary The list of experiment summaries.
 */
fun OutputStream.writeCsv(summary: List<ExperimentSummary>) {
    val writer = bufferedWriter()
    writer.write("\"system\",\"property\",\"total simulations\",\"total time\",\"simulations for equivalence testing\",\"simulation time\",\"falsified\",\"input\"")
    writer.newLine()
    for (s in summary) {
        val line = "${s.system},${s.property},${s.totalSimulations},${s.totalTime},${s.simulationsForEqTest},${s.simulationTime},${s.falsified},${s.input}"
        writer.write(line)
        writer.newLine()
    }
    writer.flush()
}

/**
 * Run the experiment with the given verifier.
 *
 * @param verifier The verifier to run the experiment.
 * @param systemName The name of the system.
 * @param propertyName The name of the property.
 * @return The summary of the experiment.
 */
fun runExperiment(verifier: NumericSULVerifier, systemName: String = "", propertyName: String = ""):  ExperimentSummary {
    val timer = TimeMeasure()
    timer.start()
    val result = verifier.run()
    timer.stop()

    // Print the result
    if (result) {
        logger.info("The property is likely satisfied")
    } else {
        for (i in 0 until verifier.cexProperty.size) {
            logger.info("${verifier.cexProperty[i]} is falsified by the following counterexample")
            logger.info("cex concrete input: ${verifier.cexConcreteInput[i]}")
            logger.info("cex abstract input: ${verifier.cexAbstractInput[i]}")
            logger.info("cex output: ${verifier.cexOutput[i]}")
        }
    }
    logger.info("Total execution time: ${timer.getSecond()} [sec]")
    logger.info("Execution time for simulation: ${verifier.simulationTimeSecond} [sec]")
    logger.info("Number of simulations: ${verifier.simulinkCount}")
    logger.info("Number of simulations for equivalence testing: ${verifier.simulinkCountForEqTest}")

    return ExperimentSummary(
        systemName,
        propertyName,
        verifier.simulinkCount,
        timer.getSecond(),
        verifier.simulinkCountForEqTest,
        verifier.simulationTimeSecond,
        (if (result) "no" else "yes"),
        (if (result) "" else "\"${verifier.cexConcreteInput[0]}\"")
    )
}
