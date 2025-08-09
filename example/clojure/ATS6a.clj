;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NAME
;;   ATS6a.clj
;; DESCRIPTION
;;   Script to falsify the automatic transmission benchmark against the S6a formula by FalCAuN
;; AUTHOR
;;   Masaki Waga
;; HISTORY
;;   2025/08/09: Initial Clojure port from kotlin/ATS6a.main.kts
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
;;   lein exec -p ATS6a.clj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(import '(net.maswag.falcaun
          AdaptiveSTLList
          ArgParser$GASelectionKind
          InputMapperReader
          NumericSULMapper
          NumericSULVerifier
          OutputMapperReader
          SimulinkSUL
          STLFactory))

(load-file "common.clj")
(load-file "auto_trans.clj")

;; Reduce verbose logs
(suppress-logs)

;; Define the input and output mappers
(def input-mapper
  (let [throttle-values [0.0 50.0 100.0]
        brake-values    [0.0 325.0]]
    (InputMapperReader/make [throttle-values brake-values])))

;; Output mapping: ignore velocity/acceleration for discretization, keep gear, and add pseudo-signals
(def output-mapper-reader
  (let [ignore-values       [nil]
        gear-values         [nil]
        velocity-values     [35.0 nil]
        acceleration-values [3000.0 nil]]
    ;; Note: order is [ignore, ignore, gear, velocity, acceleration]
    (doto (OutputMapperReader. [ignore-values ;; velocity
                                ignore-values ;; acceleration
                                gear-values ;; gear
                                velocity-values ;; previous_min(velocity)
                                acceleration-values]) ;; previous_min(acceleration)
      (.parse))))

;; Extended signal mapper for previous_max_output(0) and previous_max_output(1)
(def mapper
  (make-mapper input-mapper output-mapper-reader
               ["previous_max_output(0)"
                "previous_max_output(1)"]))

;; Define the STL properties
(def stl-list
  (let [horizon-rot (int (/ 30.0 signal-step))
        horizon-vel (int (/ 4.0 signal-step))
        prev-max-velocity "output(3)"
        prev-max-rotation "output(4)"
        stl-not-g-rot-lt3000 (format "<>_[0,%d] (%s > 3000.0)" horizon-rot prev-max-rotation)
        stl-g-vel-lt35        (format "[]_[0,%d] (%s < 35.0)"  horizon-vel prev-max-velocity)
        stl-str               (format "(%s) || (%s)" stl-not-g-rot-lt3000 stl-g-vel-lt35)]
    (parse-stl-list
     [stl-str]
     input-mapper
     output-mapper-reader)))

(def signal-length 30)
(def properties (AdaptiveSTLList. stl-list signal-length))

;; Build the automatic transmission model and set up the verifier
(def autotrans
  (build-autotrans))
;; Constants for the GA-based equivalence testing
(def max-test 50000)
(def population-size 200)
(def crossover-prob 0.5)
(def mutation-prob 0.01)
(def timeout-minutes 50)

(def verifier
  (make-verifier autotrans signal-step properties mapper signal-length
                max-test population-size crossover-prob mutation-prob timeout-minutes))

;; Run the verifier
(def result (.run verifier))
(.close autotrans)

;; Show the results
(print-results verifier result)
(print-stats verifier)

