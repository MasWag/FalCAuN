(import '(java.io BufferedReader StringReader))
(import '(net.maswag.falcaun
          ExtendedSignalMapper
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

  - verifier: a FalCAuN verifier exposing counterexample accessors
    (`getCexProperty`, `getCexConcreteInput`, `getCexAbstractInput`, `getCexOutput`).
  - result: boolean; true if all properties are (likely) satisfied.

  Prints either a success message or each falsified property with its
  concrete/abstract inputs and observed outputs."
  [verifier result]
  (if result
    (println "All the properties are likely satisfied")
    (do
      (println "Some properties are falsified")
      (let [properties (.getCexProperty verifier)
            concrete-inputs (.getCexConcreteInput verifier)
            abstract-inputs (.getCexAbstractInput verifier)
            outputs (.getCexOutput verifier)]
        (doseq [[prop cin ain out] (map vector properties concrete-inputs abstract-inputs outputs)]
          (do
            (printf "%s is falsified by the following counterexample:\n" prop)
            (printf "cex concrete input: %s\n" cin)
            (printf "cex abstract input: %s\n" ain)
            (printf "cex output: %s\n" out)))))))

(defn print-discrete-results
  "Pretty-print verification results for discrete alphabets.

  - verifier: a FalCAuN verifier exposing `getCexProperty`, `getCexInput`, `getCexOutput`.
  - result: boolean; true if all properties are (likely) satisfied.

  Prints either a success message or each falsified property with its
  discrete input trace and observed outputs."
  [verifier result]
  (if result
    (println "All the properties are likely satisfied")
    (do
      (println "Some properties are falsified")
      (let [properties (.getCexProperty verifier)
            inputs     (.getCexInput verifier)
            outputs (.getCexOutput verifier)]
        (doseq [[prop in out] (map vector properties inputs outputs)]
          (do
            (printf "%s is falsified by the following counterexample:\n" prop)
            (printf "cex input: %s\n" in)
            (printf "cex output: %s\n" out)))))))

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
    `getSimulinkCount`, and `getSimulinkCountForEqTest`.

  Prints execution time and the number of simulations performed."
  [verifier]
  (printf "Execution time for simulation: %g [sec]\n"
          (.getSimulationTimeSecond verifier))
  (println "Number of simulations: " (.getSimulinkCount verifier))
  (println "Number of simulations for equivalence testing: "
           (.getSimulinkCountForEqTest verifier)))
