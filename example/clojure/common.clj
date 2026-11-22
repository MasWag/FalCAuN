(import '(java.io BufferedReader StringReader))
(import '(org.slf4j LoggerFactory))
(import '(ch.qos.logback.classic Level Logger))
(import '(net.automatalib.modelchecker.ltsmin AbstractLTSmin LTSminVersion))
(import '(net.maswag.falcaun
          AbstractAdaptiveSTLUpdater
          AdaptiveSTLList
          GASelectionKind
          EQSearchProblem
          EQSteadyStateGeneticAlgorithm
          ExtendedSignalMapper
          InputMapperReader
          NumericSULMapper
          NumericSULVerifier
          OutputMapperReader))
(import '(net.maswag.falcaun.parser
          STLFactory))

(defn make-signal-deriver
  "Construct an ExtendedSignalMapper from mapping expressions.

  - expr: zero or more strings, each a line of extended signal
    mapping to be parsed by FalCAuN (e.g., \"previous_max_output(0)\").

  Returns an instance of `ExtendedSignalMapper`. If no expressions are
  provided, returns an empty mapper (no derived signals)."
  [& expr]
  (let [mapper-str (clojure.string/join "\n" expr)]
    (if (empty? expr)
      (ExtendedSignalMapper.)
      (ExtendedSignalMapper/parse
       (BufferedReader. (StringReader. mapper-str))))))

(defn print-results
  "Pretty-print verification results for numeric/continuous signals.

  - verifier: a FalCAuN `NumericSULVerifier` used to construct the concrete inputs.
  - result: the `VerificationResult` returned by `(.run verifier)`.

  Prints each property falsified by a counterexample confirmed by the SUL with its
  concrete/abstract inputs and observed outputs. If no counterexample is found,
  the result is inconclusive: it does not prove the properties."
  [verifier result]
  (let [cexs (.confirmedCounterexamples result)]
    (if (.isEmpty cexs)
      (println "No counterexample is found (termination reason:" (str (.reason result)) ")")
      (do
        (if (.allTargetsFalsified result)
          (println "All the properties are falsified")
          (println "Some properties are falsified"))
        (doseq [cex cexs]
          (printf "%s is falsified by the following counterexample:\n" (.property cex))
          (printf "cex concrete input: %s\n" (.concreteInput verifier cex))
          (printf "cex abstract input: %s\n" (.abstractInput cex))
          (printf "cex output: %s\n" (.sutOutput cex)))))))

(defn print-discrete-results
  "Pretty-print verification results for discrete alphabets.

  - verifier: a FalCAuN verifier (unused; kept for symmetry with `print-results`).
  - result: the `VerificationResult` returned by `(.run verifier)`.

  Prints each property falsified by a counterexample confirmed by the SUL with its
  discrete input trace and observed outputs. If no counterexample is found,
  the result is inconclusive: it does not prove the properties."
  [_verifier result]
  (let [cexs (.confirmedCounterexamples result)]
    (if (.isEmpty cexs)
      (println "No counterexample is found (termination reason:" (str (.reason result)) ")")
      (do
        (if (.allTargetsFalsified result)
          (println "All the properties are falsified")
          (println "Some properties are falsified"))
        (doseq [cex cexs]
          (printf "%s is falsified by the following counterexample:\n" (.property cex))
          (printf "cex input: %s\n" (.abstractInput cex))
          (printf "cex output: %s\n" (.sutOutput cex)))))))

(defn parse-stl-list
  "Parse a list of STL formulas using the given mappers.

  - stl-list: sequence of STL strings.
  - input-mapper: `InputMapperReader` instance (domain discretization).
  - output-mapper-reader: `OutputMapperReader` (range discretization) with
    accessible output mapper and largest symbols.

  Returns a sequence of compiled STL properties (via `STLFactory`)."
  [stl-list input-mapper output-mapper-reader]
  (let [stl-factory (STLFactory.)
        output-mapper (.getOutputMapper output-mapper-reader)
        largest (.getLargest output-mapper-reader)]
    (map (fn [stl-string]
           (.parse
            stl-factory
            stl-string
            input-mapper
            output-mapper
            largest))
         stl-list)))

(defn print-stats
  "Print summary statistics from a FalCAuN verifier run.

  - verifier: a verifier exposing `getSimulationTimeSecond`,
    `getSutExecutionCount`, and `getEqEvaluationCount`.

  Prints execution time and the number of simulations performed."
  [verifier]
  (printf "Execution time for simulation: %g [sec]\n"
          (.getSimulationTimeSecond verifier))
  (println "Number of simulations: " (.getSutExecutionCount verifier))
  (println "Number of simulations for equivalence testing: "
           (.getEqEvaluationCount verifier)))

(defn suppress-logs
  "Adjust logger levels to reduce verbose output.
   
   Sets several FalCAuN/LTSmin-related loggers to INFO to suppress
   debug/trace messages during runs of the examples."
  []
  (let [set-level (fn [class-name]
                    (let [logger (LoggerFactory/getLogger class-name)]
                      (.setLevel logger Level/INFO)))]
    (set-level AbstractAdaptiveSTLUpdater)
    (set-level AdaptiveSTLList)
    (set-level LTSminVersion)
    (set-level AbstractLTSmin)
    (set-level EQSearchProblem)
    (set-level EQSteadyStateGeneticAlgorithm)))

(defn make-mapper
  "Create a NumericSULMapper from input and output mappers.
   
   - input-mapper: InputMapperReader instance.
   - output-mapper-reader: OutputMapperReader instance.
   - signal-deriver-exprs: Optional expressions for the signal deriver.
   
   Returns a NumericSULMapper instance."
  ([input-mapper output-mapper-reader]
   (make-mapper input-mapper output-mapper-reader []))
  ([input-mapper output-mapper-reader signal-deriver-exprs]
   (let [signal-deriver (apply make-signal-deriver signal-deriver-exprs)]
     (NumericSULMapper.
      input-mapper
      output-mapper-reader
      signal-deriver))))

(defn make-verifier
  "Create a NumericSULVerifier with common configuration.
   
   - sul: The system under learning.
   - signal-step: Step size for the signal.
   - properties: AdaptiveSTLList of properties to verify.
   - mapper: NumericSULMapper instance.
   - signal-length: Length of the signal.
   - max-test: Maximum number of tests.
   - population-size: GA population size.
   - crossover-prob: GA crossover probability.
   - mutation-prob: GA mutation probability.
   - timeout-minutes: Timeout in minutes.
   
   Returns a configured NumericSULVerifier instance."
  ([sul signal-step properties mapper signal-length]
   (make-verifier sul signal-step properties mapper signal-length 20))
  ([sul signal-step properties mapper signal-length max-test]
   (make-verifier sul signal-step properties mapper signal-length max-test 50))
  ([sul signal-step properties mapper signal-length max-test population-size]
   (make-verifier sul signal-step properties mapper signal-length max-test population-size 0.5))
  ([sul signal-step properties mapper signal-length max-test population-size crossover-prob]
   (make-verifier sul signal-step properties mapper signal-length max-test population-size crossover-prob 0.01))
  ([sul signal-step properties mapper signal-length max-test population-size crossover-prob mutation-prob]
   (make-verifier sul signal-step properties mapper signal-length max-test population-size crossover-prob mutation-prob 10))
  ([sul signal-step properties mapper signal-length max-test population-size crossover-prob mutation-prob timeout-minutes]
   (doto (NumericSULVerifier. sul signal-step properties mapper)
     (.setTimeout (* timeout-minutes 60))
     (.addCornerCaseEQOracle signal-length (/ signal-length 2))
     (.addGAEQOracleAll
      signal-length
      max-test
      GASelectionKind/Tournament
      population-size
      crossover-prob
      mutation-prob))))
