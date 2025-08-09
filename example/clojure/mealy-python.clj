;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; NAME
;;   mealy-python.clj
;; DESCRIPTION
;;   Verify LTL properties of a Python-implemented Mealy SUL using FalCAuN
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
;;   lein exec -p mealy-python.clj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(import '(java.util Random))
(import '(net.automatalib.alphabet Alphabets))

(import '(de.learnlib.oracle.membership SULOracle))
(import '(net.maswag.falcaun
          AdaptiveSTLList
          BlackBoxVerifier
          LTLFactory
          PythonSUL))

;; Path to the Python SUL. We keep it local to the clojure dir.
(def python-file "./mealy_python.py")

;; Define LTL properties
(def properties
  (let* [ltl-factory (LTLFactory.)
         ltl-list (map (fn [s] (.parse ltl-factory s))
                       ["[] (output == p -> X (output == q))" ; does not hold
                        "[] ((input == a && output == p && (X input == a)) -> (X output == q))"]) ; holds
         signal-length 10]
    (AdaptiveSTLList. ltl-list signal-length)))

;; Define the SUL and oracle
(def sul (PythonSUL. python-file String))
(def oracle (SULOracle. sul))
(.setMemOracle properties oracle)

;; Input alphabet
(def sigma (Alphabets/fromList ["a" "b"]))

;; Configure and run the verifier
(def verifier 
  (doto (BlackBoxVerifier. oracle sul properties sigma)
    ;; Timeout must be set before adding equivalence testing
    (.setTimeout (* 5 60)) ; 5 minutes
    (.addRandomWordEQOracle
     1   ; min length
     10  ; max length
     1000 ; max tests
     (Random.)
     1)))

(def result (.run verifier))

;; Print the result
(print-discrete-results verifier result)
