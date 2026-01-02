;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NAME
;;   simglucose4.clj
;; DESCRIPTION
;;   Verify STL properties on the simglucose Python environment (case 4)
;; AUTHOR
;;   Masaki Waga
;; HISTORY
;;   2025/08/16: Initial implementation
;; COPYRIGHT
;;   Copyright (c) 2025 Masaki Waga
;;   Released under the MIT license
;;   https://opensource.org/licenses/mit-license.php
;;
;; USAGE
;;   JEP_JAVA_LIBRARY_PATH="/path/to/site-packages/jep" \
;;   PYTHONEXECUTABLE="/path/to/python3.10" \
;;   lein exec -p simglucose4.clj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(import '(java.util Random))
(import '(net.maswag.falcaun
          AdaptiveSTLList))
(import '(net.maswag.falcaun.parser
          STLFactory))

(load-file "common.clj")
(load-file "simglucose.clj")

;; Reduce verbose logs
(suppress-logs)

;; Define input and output mappers
(def input-mapper (make-default-input-mapper))

;; Output mapping: [ignoreValues, insulinValues, minbgValues, maxbgValues, deltaBgValues, deltaBgValues]
(def output-mapper-reader
  (let [ignore-values   [nil]
        min-bg-values   [70.0 nil]
        max-bg-values   [180.0 nil]
        insulin-values  [nil]
        delta-bg-values [-5.0 3.0 nil]]
    (OutputMapperReader. [ignore-values insulin-values min-bg-values max-bg-values delta-bg-values delta-bg-values])))

(def mapper (make-mapper input-mapper output-mapper-reader))

;; Define the STL properties
(def stl-list
  (parse-stl-list
   [;; BG must be in a good range
    (format "G(%s > 70.0)" min-bg)
    (format "G(%s < 180.0)" max-bg)
    ;; BG must be below 180 if the meal is not given too much
    (format "(G_[0,5] %s == 50.0) R (%s < 180.0)" meal-size max-bg)
    ;; The change in BG is between -5 and 3
    (format "G(%s > -5.0 && %s < 3.0)" min-delta-bg max-delta-bg)
    ;; The change in BG is between -5 and 3 if the meal is not given too much
    (format "(G_[0,5] %s == 50.0) R (%s > -5.0 && %s < 3.0)" meal-size min-delta-bg max-delta-bg)]
   input-mapper
   output-mapper-reader))

(def properties (AdaptiveSTLList. stl-list default-signal-length))

;; Constants for the GA-based equivalence testing
(def max-test 50000)
(def population-size 200)
(def crossover-prob 0.5)
(def mutation-prob 0.01)
(def timeout-minutes 40)

;; Build Python SUL and verifier
(def sul (make-simglucose-sul))
(def verifier (make-verifier sul signal-step properties mapper default-signal-length
                            max-test population-size crossover-prob mutation-prob timeout-minutes))

;; Run verification
(def result (.run verifier))

;; Show result and stats
(print-results verifier result)
(print-stats verifier)
