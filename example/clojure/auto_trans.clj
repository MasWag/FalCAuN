;; Clojure definitions for AutoTrans

(def init-script "
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
  ["throttle" "brake"])

;; Sampling step for input signal (seconds)
(def signal-step 1.0)

;; Fixed-step size used in Simulink simulation (seconds)
(def simulink-simulation-step 0.0025)
