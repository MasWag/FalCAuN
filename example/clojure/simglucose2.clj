;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NAME
;;   simglucose2.clj
;; DESCRIPTION
;;   Verify STL properties on the simglucose Python environment (case 2)
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
;;   lein exec -p simglucose2.clj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(import '(java.util Random))
(import '(net.maswag.falcaun
          AdaptiveSTLList
          STLFactory))

(load-file "common.clj")
(load-file "simglucose.clj")

;; Reduce verbose logs
(suppress-logs)

;; Define input and output mappers
(def input-mapper (make-default-input-mapper))

;; Output mapping: [bgValues, insulinValues, ignore, bgValues, ignore, ignore]
>>>>>>> 72f25fe (Simplified the examples in Clojure)
(def output-mapper-reader
  (let [ignore-values   [nil]
        bg-values       [55.0 70.0 400.0]
        insulin-values  [0.5]]
    (OutputMapperReader. [bg-values insulin-values ignore-values bg-values ignore-values ignore-values])))

(def mapper (make-mapper input-mapper output-mapper-reader))
(def alpha 5)

;; Define STL properties
(def stl-list
  (parse-stl-list
   [;; BG does not go above 400
    (format "(input(0) == 50.0 && X (input(0) == 50.0)) R (%s < 400.0)" max-bg)
    ;; Does not fall below the lower 10% for more than 30 minutes
    (format "(input(0) == 50.0 && X (input(0) == 50.0)) R (%s < 70.0 -> X (%s > 70.0))" bg max-bg)
    ;; Hypoglycemia does not last longer than 150 minutes
    (format "(<> (input(0) == 50.0 && X (input(0) == 50.0))) R ! []_[0,%d] (%s < 70.0)" alpha max-bg)
    ;; Does not administer insulin when hypoglycemia
    (format "(input(0) == 50.0 && X (input(0) == 50.0)) R (%s < 70.0) -> (%s < 0.5)" bg insulin)]
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

