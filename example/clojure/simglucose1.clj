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
          ArgParser$GASelectionKind
          InputMapperReader
          NumericSULMapper
          NumericSULVerifier
          OutputMapperReader
          PythonNumericSUL
          STLFactory))

(load-file "common.clj")

;; Step size (seconds) per high-level step sent to Python SUL
(def signal-step 1.0)
;; Python initialization script implementing SUL
(def init-script "./simglucose_example.py")

;; Define input and output mappers (match simglucose_example.py return shape)
(def input-mapper
  (let [meal-size-values [0.0 50.0]]
    (InputMapperReader/make [meal-size-values])))

;; Output: [last_bg, sum_insulin, min_bg, max_bg, min_delta_bg, max_delta_bg]
(def output-mapper-reader
  (let [bg-values       [90.0]
        ignore-values   [nil]
        delta-bg-values [-5.0 3.0]]
    (doto (OutputMapperReader. [bg-values ignore-values ignore-values ignore-values delta-bg-values delta-bg-values])
      (.parse))))

(def mapper
  (let [signal-deriver (make-signal-deriver)]
    (NumericSULMapper.
     input-mapper
     (.getLargest output-mapper-reader)
     (.getOutputMapper output-mapper-reader)
     signal-deriver)))

;; Helpful aliases for signals in STL formulas
(def bg "signal(0)")
(def insulin "signal(1)")
(def min-bg "signal(2)")
(def max-bg "signal(3)")
(def min-dbg "signal(4)")
(def max-dbg "signal(5)")

;; Define STL properties
(def stl-list
  (parse-stl-list
   [;; If BG is not low, insulin administration accompanies the diet
    (format "(%s > 90.0 -> (input(0) > 0 -> %s > 0.5))" bg insulin)
    ;; The change in BG is between -5 and 3 with weak-release over two steps of input>0
    (format "((input(0) > 0.0 && X (input(0) > 0.0))) R (%s > -5.0 && %s < 3.0)" min-dbg max-dbg)]
   input-mapper
   output-mapper-reader))

(def signal-length 48) ; 3*10 * 24 mins
(def properties (AdaptiveSTLList. stl-list signal-length))

;; GA-based equivalence testing params
(def max-test 20)           ; aggressively reduced for fast runs
(def population-size 50)
(def crossover-prob 0.5)
(def mutation-prob 0.01)

;; Build Python SUL
(def sul (PythonNumericSUL. init-script))
(def verifier
  (doto (NumericSULVerifier. sul signal-step properties mapper)
    ;; Lower timeout to keep runtime reasonable
    (.setTimeout (* 5 60 2)) ; 10 minutes
    (.addCornerCaseEQOracle signal-length (/ signal-length 2))
    (.addGAEQOracleAll
     signal-length
     max-test
     ArgParser$GASelectionKind/Tournament
     population-size
     crossover-prob
     mutation-prob)))

(def result (.run verifier))

;; Show result and stats
(print-results verifier result)
(print-stats verifier)
