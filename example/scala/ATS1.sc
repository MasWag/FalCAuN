#!/usr/bin/env -S scala-cli

//> using repository m2Local
//> using dep "net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT"
//> using dep "net.maswag.falcaun:FalCAuN-matlab:1.0-SNAPSHOT"
//> using file "AutoTrans.scala"

/*****h* scala/ATS1
 *  NAME
 *   ATS1.sc
 *  DESCRIPTION
 *   Script to falsify the automatic transmission benchmark against the S1 formula by FalCAuN
 *  AUTHOR
 *   Masaki Waga
 *  HISTORY
 *    - 2025/08/09: Initial version
 *  COPYRIGHT
 *   Copyright (c) 2025 Masaki Waga
 *   Released under the MIT license
 *   https://opensource.org/licenses/mit-license.php
 *
 *  PORTABILITY
 *   This script assumes the following:
 *   - FalCAuN is installed, for example, by mvn install.
 *   - The environment variable MATLAB_HOME is set to the root directory of MATLAB, e.g., /Applications/MATLAB_R2024a.app/ or /usr/local/MATLAB/R2024a.
 *
 *  USAGE
 *   ./ATS1.sc
 *
 ********/

import net.maswag.falcaun.*
import scala.jdk.CollectionConverters.*

// Import AutoTrans model constants (defined in AutoTrans.scala)
import net.maswag.falcaun.{initScript, paramNames, signalStep, simulinkSimulationStep}

// (Optional) logging tweaks removed to avoid extra dependencies

// Define the input and output mappers
val throttleValues = List[java.lang.Double](0.0, 100.0).asJava
val brakeValues = List[java.lang.Double](0.0, 325.0).asJava
val inputMapper = InputMapperReader.make(List(throttleValues, brakeValues).asJava)
val velocityValues = List[java.lang.Double](20.0, 40.0, 60.0, 80.0, 100.0, 120.0, null).asJava

val accelerationValues = List[java.lang.Double](null).asJava
val gearValues = List[java.lang.Double](null).asJava

val outputMapperReader = new OutputMapperReader(List(velocityValues, accelerationValues, gearValues).asJava)
outputMapperReader.parse()

val signalMapper = new ExtendedSignalMapper()
val mapper = new NumericSULMapper(
  inputMapper,
  outputMapperReader.getLargest(),
  outputMapperReader.getOutputMapper(),
  signalMapper
)

// Define the STL properties
val stlFactory = new STLFactory()
val stlListJava = List(
  "[] (signal(0) < 120)",
  "[] (signal(0) < 100)",
  "[] (signal(0) < 80)",
  "[] (signal(0) < 60)",
  "[] (signal(0) < 40)",
  "[] (signal(0) < 20)"
).map { stlString =>
  stlFactory.parse(
    stlString,
    inputMapper,
    outputMapperReader.getOutputMapper(),
    outputMapperReader.getLargest()
  )
}.asJava

val signalLength = 30
val properties = new AdaptiveSTLList(stlListJava, signalLength)

// Constants for the GA-based equivalence testing
val maxTest = 50000
val populationSize = 200
val crossoverProb = 0.5
val mutationProb = 0.01

// Load the automatic transmission model and run the verifier
val autoTransSUL = new SimulinkSUL(initScript, paramNames, signalStep, simulinkSimulationStep)
try {
  val verifier = new NumericSULVerifier(autoTransSUL, signalStep, properties, mapper)
  verifier.setTimeout(5 * 60) // seconds
  verifier.addCornerCaseEQOracle(signalLength, signalLength / 2)
  verifier.addGAEQOracleAll(
    signalLength,
    maxTest,
    ArgParser.GASelectionKind.Tournament,
    populationSize,
    crossoverProb,
    mutationProb
  )

  val result = verifier.run()

  if (result) {
    println("The property is likely satisfied")
  } else {
    val props          = verifier.getCexProperty().asScala
    val concreteInputs = verifier.getCexConcreteInput().asScala
    val abstractInputs = verifier.getCexAbstractInput().asScala
    val outputs        = verifier.getCexOutput().asScala

    for (i <- props.indices) {
      println(s"${props(i)} is falsified by the following counterexample")
      println(s"cex concrete input: ${concreteInputs(i)}")
      println(s"cex abstract input: ${abstractInputs(i)}")
      println(s"cex output: ${outputs(i)}")
    }
  }

  println(s"Execution time for simulation: ${verifier.getSimulationTimeSecond} [sec]")
  println(s"Number of simulations: ${verifier.getSimulinkCount}")
  println(s"Number of simulations for equivalence testing: ${verifier.getSimulinkCountForEqTest}")
} finally {
  try autoTransSUL.close() catch { case _: Throwable => () }
}
