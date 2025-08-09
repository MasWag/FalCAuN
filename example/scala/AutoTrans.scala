package net.maswag.falcaun

// Scala 3 definitions used by ATS1.sc

val initScript: String = """
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
% Bardh Hoxha, Houssam Abbas, Georgios E. Fainekos
"""

// Parameter names for Simulink inputs
val paramNames: java.util.List[String] = java.util.Arrays.asList("throttle", "brake")

// Sampling step for input signal (seconds)
var signalStep: Double = 1.0

// Fixed-step size used in Simulink simulation (seconds)
val simulinkSimulationStep: Double = 0.0025
