#!/usr/bin/env -S scala-cli

//> using repository m2Local
//> using dep "net.maswag.falcaun:FalCAuN-core:1.0-SNAPSHOT"

import de.learnlib.driver.simulator.MealySimulatorSUL
import de.learnlib.oracle.membership.SULOracle
import java.util.Random
import net.automatalib.alphabet.Alphabets
import net.automatalib.automaton.transducer.CompactMealy
import net.automatalib.util.automaton.builder.AutomatonBuilders
import net.automatalib.visualization.Visualization
import scala.jdk.CollectionConverters.*

import net.maswag.falcaun.AdaptiveSTLList
import net.maswag.falcaun.BlackBoxVerifier
import net.maswag.falcaun.LTLFactory

// Define the target Mealy machine
// 1. input alphabet contains strings "a" and "b"
val sigma = Alphabets.fromList(List("a", "b").asJava)
// 2. output alphabet contains strings "p" and "q"
val gamma = Alphabets.fromList(List("p", "q").asJava)
// 3. create Mealy machine
// @formatter:off
val target: CompactMealy[String, String] = AutomatonBuilders.newMealy[String, String](sigma)
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
    List(
        "[] (output == p -> X (output == q))", // This does not hold
        "[] ((input == a && output == p && (X input == a)) -> (X output == q))", // This holds
    ).map(ltlString =>
        ltlFactory.parse(ltlString)
    ).toList.asJava
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

  val props   = verifier.getCexProperty().asScala
  val inputs  = verifier.getCexInput().asScala
  val outputs = verifier.getCexOutput().asScala

  for (i <- 0 until props.length) {

    println(s"${props(i)} is falsified by the following counterexample:")
    println(s"cex concrete input: ${inputs(i)}")
    println(s"cex output: ${outputs(i)}")
  }
}
