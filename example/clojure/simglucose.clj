;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NAME
;;   simglucose.clj
;; DESCRIPTION
;;   Helper functions for simglucose Python environment via FalCAuN
;; AUTHOR
;;   Masaki Waga
;; HISTORY
;;   2025/08/16: Initial implementation
;; COPYRIGHT
;;   Copyright (c) 2025 Masaki Waga
;;   Released under the MIT license
;;   https://opensource.org/licenses/mit-license.php
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(import '(java.util Random))
(import '(net.maswag.falcaun
          InputMapperReader
          PythonNumericSUL))

(load-file "common.clj")

;; Python initialization script implementing SUL
(def init-script 
  "Path to the Python initialization script for simglucose."
  "./simglucose_example.py")

;; Step size (seconds) per high-level step sent to Python SUL
(def signal-step 
  "Input signal sampling step, in seconds."
  1.0)

;; Each step corresponds to 30 minutes in the simulation
(def step-duration 
  "Duration of each step in minutes."
  30.0)

;; Name of signals as string constants for STL formulas
(def meal-size "input(0)")
(def bg "signal(0)")
(def insulin "signal(1)")
(def min-bg "signal(2)")
(def max-bg "signal(3)")
(def min-delta-bg "signal(4)")
(def max-delta-bg "signal(5)")

;; Default signal length (48 steps = 24 hours)
(def default-signal-length 48)

;; Default GA-based equivalence testing parameters
(def default-max-test 50000)
(def default-population-size 200)
(def default-crossover-prob 0.5)
(def default-mutation-prob 0.01)
(def default-timeout-minutes 40)

(defn make-simglucose-sul
  "Create a Python-backed SUL for simglucose.
   
   Returns a system-under-learning instance configured with the
   init-script."
  []
  (PythonNumericSUL. init-script))

(defn make-default-input-mapper
  "Create the default input mapper for simglucose with meal size values.
   
   - meal-sizes: Vector of possible meal sizes. Default is [0.0 50.0].
   
   Returns an InputMapperReader instance."
  ([]
   (make-default-input-mapper [0.0 50.0]))
  ([meal-sizes]
   (InputMapperReader/make [meal-sizes])))



