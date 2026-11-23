(import '(net.maswag.falcaun.simulink
          SimulinkSUL))
;; Clojure definitions for AutoTrans

(defn benchmark-init-script
  "MATLAB command running the shared FalCAuN benchmark definition
  `benchmarks/simulink/<relative-path>`. The root of the FalCAuN repository
  is searched from the current working directory upwards. The script is run
  by its absolute path, so the command works regardless of the current
  directory of MATLAB. See `benchmarks/simulink/README.md`."
  [relative-path]
  (let [root (->> (.getAbsoluteFile (java.io.File. ""))
                  (iterate #(.getParentFile ^java.io.File %))
                  (take-while some?)
                  (filter #(.isDirectory (java.io.File. ^java.io.File % "benchmarks/simulink")))
                  first)
        script (when root (java.io.File. ^java.io.File root (str "benchmarks/simulink/" relative-path)))]
    (when-not (and script (.isFile script))
      (throw (ex-info (str "benchmarks/simulink/" relative-path " is not found. "
                           "Run this example inside the FalCAuN repository.")
                      {:script relative-path})))
    (str "run('" (.replace (.getCanonicalPath script) "'" "''") "');")))

(def init-script
  "MATLAB init script for the automatic transmission model [Hoxha et al.,
  ARCH@CPSWeek 2014]. See benchmarks/simulink/AT/initAT.m for the details,
  e.g., the model and the unit conversion."
  (benchmark-init-script "AT/initAT.m"))

;; Parameter names for Simulink inputs
(def param-names
  "Ordered list of Simulink input signal names."
  ["throttle" "brake"])

;; Sampling step for input signal (seconds)
(def signal-step
  "Input signal sampling step, in seconds."
  1.0)

;; Fixed-step size used in Simulink simulation (seconds)
(def simulink-simulation-step
  "Fixed-step size for the Simulink simulation, in seconds."
  0.0025)

(defn build-autotrans
  "Construct a `SimulinkSUL` for the automatic transmission model.

  Returns a system-under-learning instance configured with the
  `init-script`, `param-names`, `signal-step`, and
  `simulink-simulation-step`."
  []
  (SimulinkSUL. init-script param-names signal-step simulink-simulation-step))
