(import '(de.learnlib.driver.simulator MealySimulatorSUL))

(import '(de.learnlib.oracle.membership SULOracle))
(import '(java.util Random))
(import '(net.automatalib.alphabet Alphabets))
(import '(net.automatalib.automaton.transducer CompactMealy))
(import '(net.automatalib.util.automaton.builder AutomatonBuilders))
(import '(net.automatalib.visualization Visualization))

(import '(net.maswag.falcaun
          AdaptiveSTLList
          BlackBoxVerifier))
(import '(net.maswag.falcaun.parser
          LTLFactory))

;; Define the target Mealy machine
;; 1. input alphabet contains strings "a" and "b"
(def sigma 
  (Alphabets/fromList ["a", "b"]))
;; 2. output alphabet contains strings "p" and "q"
(def gamma 
  (Alphabets/fromList ["p", "q"]))
;; 3. create Mealy machine
(def target 
  (-> (AutomatonBuilders/newMealy sigma)
    (.withInitial "q0")
    (.from "q0")
      (.on "a")
        (.withOutput "p")
        (.to "q1")
      (.on "b")
        (.withOutput "q")
        (.to "q2")
    (.from "q1")
      (.on "a")
        (.withOutput "q")
        (.to "q0")
      (.on "b")
        (.withOutput "p")
        (.to "q3")
    (.from "q2")
        (.on "a")
          (.withOutput "p")
          (.to "q3")
        (.on "b")
          (.withOutput "p")
          (.to "q0")
    (.from "q3")
        (.on "a")
          (.withOutput "q")
          (.to "q2")
        (.on "b")
          (.withOutput "q")
          (.to "q1")
    (.create)))

;; This shows the target Mealy machine in a new window. The script is blocked until the window is closed.
(Visualization/visualize
 (.transitionGraphView target sigma))

;; Define LTL properties
(def properties
  (let* [ltlFactory (LTLFactory.)
         ltlList
         (map 
          (fn [ltlString]
            (.parse ltlFactory ltlString))
          [ ;; This does not hold
           "[] (output == p -> X (output == q))"
           ;; This holds
           "[] ((input == a && output == p && (X input == a)) -> (X output == q))"])
         ;; We believe that the traces of length 10 are enough to verify/falsify the properties
         signalLength 10
         ]
    (AdaptiveSTLList. ltlList signalLength)))

;; Define the SUL and oracle
(def sul (MealySimulatorSUL. target))
(def oracle (SULOracle. sul))
(.setMemOracle properties oracle)

;; Configure and run the verifier
(def verifier
  (BlackBoxVerifier. oracle sul properties sigma))
;; Timeout must be set before adding equivalence testing
(.setTimeout verifier 
             ;; 5 minutes
             (* 5 60))
(.addRandomWordEQOracle
 verifier
 1 ;; The minimum length of the random word
 10 ;; The maximum length of the random word
 1000 ;; The maximum number of tests
 (Random.)
 1)
(def result (.run verifier))

;; Print the result
(if result
  (println "All the properties are likely satisfied")
  (do
    (println "Some properties are falsified")
    (let [properties (.getCexProperty verifier)
          inputs (.getCexInput verifier)
          outputs (.getCexOutput verifier)]
      (doseq [[prop in out] (map vector properties inputs outputs)]
        (do 
          (printf "%s is falsified by the following counterexample:\n" prop)
          (printf "cex concrete input: %s\n" in)
          (printf "cex output: %s\n" out))))))
