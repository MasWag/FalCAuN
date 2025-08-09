;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NAME
;;   ATS1.clj
;; DESCRIPTION
;;   Script to falsify the automatic transmission benchmark against the S1 formula by FalCAuN
;; AUTHOR
;;   Masaki Waga
;; HISTORY
;;   2025/08/09: Initial version
;; COPYRIGHT
;;   Copyright (c) 2025 Masaki Waga
;;   Released under the MIT license
;;   https://opensource.org/licenses/mit-license.php
;;
;; PORTABILITY
;;   This script assumes the following:
;;   - FalCAuN is installed, for example, by mvn install.
;;   - The environment variable MATLAB_HOME is set to the root directory of MATLAB, e.g., /Applications/MATLAB_R2024a.app/ or /usr/local/MATLAB/R2024a.
;;
;; USAGE
;;   lein exec -p ATS1.clj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(import '(de.learnlib.driver.simulator MealySimulatorSUL))

(import '(de.learnlib.oracle.membership SULOracle))
(import '(java.util Random))
(import '(net.automatalib.alphabet Alphabets))
(import '(net.automatalib.automaton.transducer CompactMealy))
(import '(net.automatalib.util.automaton.builder AutomatonBuilders))
(import '(net.automatalib.visualization Visualization))

(import '(net.maswag.falcaun
          AdaptiveSTLList
          ArgParser$GASelectionKind
          BlackBoxVerifier
          ExtendedSignalMapper
          InputMapperReader
          LTLFactory
          NumericSULMapper
          NumericSULVerifier
          OutputMapperReader
          SimulinkSUL
          STLFactory))

(load-file "auto_trans.clj")

;; Define the input and output mappers
(def input-mapper
  (let [throttle-values [0.0 100.0]
        brakeValues [0.0 325.0]]
    (InputMapperReader/make [throttle-values brakeValues])))
(def output-mapper-reader
  (let [velocity-values [20.0 40.0 60.0 80.0 100.0 120.0 nil]
        acceleration-values [nil]
        gear-values [nil]]
    (OutputMapperReader. [velocity-values acceleration-values gear-values])))
(.parse output-mapper-reader)

(def mapper
  (let [signal-mapper (ExtendedSignalMapper.)]
    (NumericSULMapper.
     input-mapper
     (.getLargest output-mapper-reader)
     (.getOutputMapper output-mapper-reader)
     signal-mapper)))

;; Define the STL properties
(def stl-list
  (let [stl-factory (STLFactory.)]
    (map (fn [stl-string]
           (.parse
            stl-factory
            stl-string
            input-mapper
            (.getOutputMapper output-mapper-reader)
            (.getLargest output-mapper-reader)))
         ["[] (signal(0) < 120)"
          "[] (signal(0) < 100)"
          "[] (signal(0) < 80)"
          "[] (signal(0) < 60)"
          "[] (signal(0) < 40)"
          "[] (signal(0) < 20)"])))

(def signal-length 30)
(def properties (AdaptiveSTLList. stl-list signal-length))

;; Constants for the GA-based equivalence testing
(def max-test 50000)
(def population-size 200)
(def crossover-prob 0.5)
(def mutation-prob  0.01)

;; Load the automatic transmission model and set up the verifier
(def autotrans
  (SimulinkSUL. init-script param-names signal-step simulink-simulation-step))
(def verifier (NumericSULVerifier. autotrans signal-step properties mapper))
;; seconds
(.setTimeout verifier (* 5 60))
(.addCornerCaseEQOracle verifier signal-length (/ signal-length 2))
(.addGAEQOracleAll
 verifier
 signal-length
 max-test
 ArgParser$GASelectionKind/Tournament
 population-size
 crossover-prob
 mutation-prob)

;; Run the verifier
(def result (.run verifier))

;; Show the results
(if result
  (println "The property is likely satisfied")
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
          (printf "cex output: %s\n" out))))))

(printf "Execution time for simulation: %g [sec]\n"
        (.getSimulationTimeSecond verifier))
(println "Number of simulations: " (.getSimulinkCount verifier))
(println "Number of simulations for equivalence testing: "
         (.getSimulinkCountForEqTest verifier))
