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

(import '(net.maswag.falcaun
          AdaptiveSTLList
          GASelectionKind
          BlackBoxVerifier
          InputMapperReader
          NumericSULMapper
          NumericSULVerifier
          OutputMapperReader))
(import '(net.maswag.falcaun.simulink
          SimulinkSUL))

(load-file "common.clj")
(load-file "auto_trans.clj")

;; Reduce verbose logs
(suppress-logs)

;; Define the input and output mappers
(def input-mapper
  (let [throttle-values [0.0 100.0]
        brake-values [0.0 325.0]]
    (InputMapperReader/make [throttle-values brake-values])))

(def output-mapper-reader
  (let [velocity-values [20.0 40.0 60.0 80.0 100.0 120.0 nil]
        acceleration-values [nil]
        gear-values [nil]]
    (OutputMapperReader. [velocity-values acceleration-values gear-values])))

(def mapper (make-mapper input-mapper output-mapper-reader))

;; Define the STL properties
(def stl-list
  (parse-stl-list
   ["[] (output(0) < 120)"
    "[] (output(0) < 100)"
    "[] (output(0) < 80)"
    "[] (output(0) < 60)"
    "[] (output(0) < 40)"
    "[] (output(0) < 20)"]
   input-mapper
   output-mapper-reader))

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
(def timeout-minutes 5)

(def verifier
  (make-verifier autotrans signal-step properties mapper signal-length
                max-test population-size crossover-prob mutation-prob timeout-minutes))

;; Run the verifier
(def result (.run verifier))
(.close autotrans)

;; Show the results
(print-results verifier result)
(print-stats verifier)
