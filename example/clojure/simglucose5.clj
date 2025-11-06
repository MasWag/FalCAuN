;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NAME
;;   simglucose5.clj
;; DESCRIPTION
;;   Verify STL properties on the simglucose Python environment (case 5)
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
;;   lein exec -p simglucose5.clj
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

;; The 10th-percentile and 90th-percentile thresholds
(def tenth-bg 66.2)
(def ninetieth-bg 189.2)

;; Output mapping: [bgValues, insulinValues, minbgValues, maxbgValues, deltaBgValues, deltaBgValues]
(def output-mapper-reader
  (let [bg-values       [tenth-bg ninetieth-bg nil]
        min-bg-values   [ninetieth-bg nil]
        max-bg-values   [tenth-bg nil]
        insulin-values  [0.5 nil]
        delta-bg-values [nil]]
    (OutputMapperReader. [bg-values insulin-values min-bg-values max-bg-values delta-bg-values delta-bg-values])))

(def mapper (make-mapper input-mapper output-mapper-reader))

;; Define the STL properties
(def stl-list
  (let [minutes-to-steps (fn [minutes] (int (/ minutes step-duration)))]
    (parse-stl-list
     [;; BG should not stay below 10th-percentile threshold for more than 120 minutes
      (format "G(%s > %s || F_[0, %d] %s > %s)" bg tenth-bg (minutes-to-steps 120) max-bg tenth-bg)
      ;; BG should not stay above 90th-percentile threshold for more than 120 minutes
      (format "G(%s < %s || F_[0, %d] %s < %s)" bg ninetieth-bg (minutes-to-steps 120) min-bg ninetieth-bg)
      ;; BG should not stay above 90th-percentile threshold for more than 90 minutes after an insulin injection
      (format "G(%s < %s || %s < 0.5 || F_[0, %d] %s < %s)" bg ninetieth-bg insulin (minutes-to-steps 90) min-bg ninetieth-bg)]
     input-mapper
     output-mapper-reader)))

;; Use a shorter signal length for this example
(def signal-length 30)
(def properties (AdaptiveSTLList. stl-list signal-length))

;; Constants for the GA-based equivalence testing
(def max-test 50000)
(def population-size 200)
(def crossover-prob 0.5)
(def mutation-prob 0.01)
(def timeout-minutes 40)

;; Build Python SUL and verifier
(def sul (make-simglucose-sul))
(def verifier (make-verifier sul signal-step properties mapper signal-length
                            max-test population-size crossover-prob mutation-prob timeout-minutes))

;; Run verification
(def result (.run verifier))

;; Show result and stats
(print-results verifier result)
(print-stats verifier)
