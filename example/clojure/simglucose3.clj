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
          STLFactory))

(load-file "common.clj")
(load-file "simglucose.clj")

;; Reduce verbose logs
(suppress-logs)

;; Define input and output mappers
(def input-mapper (make-default-input-mapper))

;; Output mapping: [bgValues, insulinValues, bgValues, ignore, ignore, ignore]
(def output-mapper-reader
  (let [ignore-values   [nil]
        bg-values       [55.0 180.0 240.0]
        insulin-values  [0.5]]
    (OutputMapperReader. [bg-values insulin-values bg-values ignore-values ignore-values ignore-values])))

(def mapper (make-mapper input-mapper output-mapper-reader))
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

