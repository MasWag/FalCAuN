;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NAME
;;   simglucose3.clj
;; DESCRIPTION
;;   Verify STL properties on the simglucose Python environment (case 3)
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
;;   lein exec -p simglucose3.clj
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

;; Define input and output mappers
(def input-mapper
  (let [meal-size-values [0.0 50.0]]
    (InputMapperReader/make [meal-size-values])))

;; Output mapping as in the Kotlin script:
;; [bgValues, insulinValues, bgValues, ignore, ignore, ignore]
(def output-mapper-reader
  (let [ignore-values   [nil]
        bg-values       [55.0 180.0 240.0]
        insulin-values  [0.5]]
    (doto (OutputMapperReader. [bg-values insulin-values bg-values ignore-values ignore-values ignore-values])
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
(def alpha 6)

;; Define STL properties
(def stl-list
  (parse-stl-list
   [;; BG does not go below 55
    (format "[] (%s > 55.0)" min-bg)
    ;; Does not exceed the upper 10% for more than 30 minutes
    (format "(input(0) == 50.0 && X (input(0) == 50.0)) R (%s > 180.0 -> X (%s < 180.0))" bg min-bg)
    ;; Does not exceed the upper 10% for more than 30 minutes after insulin administration
    (format "(input(0) == 50.0 && X (input(0) == 50.0)) R (%s > 0.5 -> X (%s < 180.0))" insulin min-bg)
    ;; Hyperglycemia does not last longer than 180 minutes
    (format "(<> (input(0) == 50.0 && X (input(0) == 50.0))) R ! []_[0,%d] (%s > 240.0)" alpha min-bg)]
   input-mapper
   output-mapper-reader))

(def signal-length 48)
(def properties (AdaptiveSTLList. stl-list signal-length))

;; GA-based equivalence testing params (reduced)
(def max-test 20)
(def population-size 50)
(def crossover-prob 0.5)
(def mutation-prob 0.01)

;; Build Python SUL and verifier
(def sul (PythonNumericSUL. init-script))
(def verifier
  (doto (NumericSULVerifier. sul signal-step properties mapper)
    (.setTimeout (* 5 60 2))
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

