;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NAME
;;   simglucose1.clj
;; DESCRIPTION
;;   Verify STL properties on the simglucose Python environment via FalCAuN
;; AUTHOR
;;   Masaki Waga
;; HISTORY
;;   2025/08/10: Initial Clojure port
;; COPYRIGHT
;;   Copyright (c) 2025 Masaki Waga
;;   Released under the MIT license
;;   https://opensource.org/licenses/mit-license.php
;;
;; USAGE
;;   JEP_JAVA_LIBRARY_PATH="/path/to/site-packages/jep" \
;;   PYTHONEXECUTABLE="/path/to/python3.10" \
;;   lein exec -p simglucose1.clj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(import '(java.util Random))
(import '(net.maswag.falcaun
          AdaptiveSTLList
          STLFactory))

(load-file "common.clj")
(load-file "simglucose.clj")

;; Reduce verbose logs
(suppress-logs)

;; Define input and output mappers (match simglucose_example.py return shape)
(def input-mapper (make-default-input-mapper))

;; Output: [last_bg, sum_insulin, min_bg, max_bg, min_delta_bg, max_delta_bg]
(def output-mapper-reader
  (let [bg-values       [90.0 nil]
        ignore-values   [nil]
        delta-bg-values [-5.0 3.0 nil]]
    (OutputMapperReader. [ignore-values ignore-values ignore-values bg-values delta-bg-values delta-bg-values])))

(def mapper (make-mapper input-mapper output-mapper-reader))

;; Alias min-dbg and max-dbg for this specific case
(def min-dbg min-delta-bg)
(def max-dbg max-delta-bg)

;; Define STL properties
(def stl-list
  (parse-stl-list
   [;; If BG is not low, insulin administration accompanies the diet
    ;; We use || instead of -> because specification strengthening does not support -> yet
    (format "G(%s < 90.0 || %s != 50 || %s > 0.5)" max-bg meal-size insulin)
    ;; The change in BG is between -5 and 3 with weak-release over two steps of input>0
    (format "((input(0) > 0.0 && X (input(0) > 0.0))) R (%s > -5.0 && %s < 3.0)" min-dbg max-dbg)]
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
