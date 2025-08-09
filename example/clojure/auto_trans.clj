(import '(net.maswag.falcaun
          SimulinkSUL))
;; Clojure definitions for AutoTrans

(def init-script
  "MATLAB init script for the automatic transmission Simulink model.

  Adds the example path based on the MATLAB release, then loads the
  `Autotrans_shift` model used in the FalCAuN benchmarks."
  "
%% Init Script for the Automatic transmission  model
% We use the automatic transmission model in [Hoxha et al.,
% ARCH@CPSWeek 2014].

%% Add the example directory to the path
versionString = version('-release');
oldpath = path;
path(strcat(userpath, '/Examples/R', versionString, '/simulink_automotive/ModelingAnAutomaticTransmissionControllerExample/'), oldpath);

%% Load the AT model
mdl = 'Autotrans_shift';
load_system(mdl);

%% References
% * [Hoxha et al., ARCH@CPSWeek 2014]: *Benchmarks for Temporal
% Logic Requirements for Automotive Systems*, ARCH@CPSWeek 2014,
% Bardh Hoxha, Houssam Abbas, Georgios E. Fainekos")

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
