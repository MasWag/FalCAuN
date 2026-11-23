%% Init Script for the Abstract Fuel Control (AFC) benchmark
% We use the abstract fuel control model in [Jin et al., HSCC'14].
%
% Usage (the absolute path makes MATLAB run exactly this file):
%   run('<FalCAuN>/benchmarks/simulink/AFC/initAFC.m');
% This script defines `mdl` and the model parameters in the caller's workspace,
% as FalCAuN expects from an initialization script. See ../README.md and
% ../third_party/README.md.

%% Load the AFC model from the pinned Breach submodule by its absolute path
% A model with the same name elsewhere on the MATLAB path is never used instead.
falcaunBenchmarkDir = fileparts(mfilename('fullpath')); % directory of this script
falcaunPreviousDir = cd(falcaunBenchmarkDir); % resolve '..' and relative paths
falcaunBenchmarkDir = pwd;
cd(falcaunPreviousDir);
modelFile = fullfile(fileparts(falcaunBenchmarkDir), 'third_party', 'breach', 'Ext', 'Models', 'AbstractFuelControl.slx');
if ~isfile(modelFile)
    error('FalCAuN:missingSubmodule', ['Simulink model not found: %s\n' ...
        'Initialize the Git submodules of FalCAuN with: git submodule update --init --recursive'], modelFile);
end
mdl = 'AbstractFuelControl';
if bdIsLoaded(mdl) && ~strcmp(get_param(mdl, 'FileName'), modelFile)
    close_system(mdl, 0);
end
load_system(modelFile);
clear falcaunBenchmarkDir falcaunPreviousDir modelFile;

%% Parameters for AFC model
fuel_inj_tol = 1.0; 
MAF_sensor_tol = 1.0;
AF_sensor_tol = 1.0; 
pump_tol = 1.;
kappa_tol=1; 
tau_ww_tol=1;
fault_time=50;
kp = 0.04;
ki = 0.14;

%% References
% * [Jin et al., HSCC'14]: *Powertrain Control Verification
% Benchmark*, HSCC 2014, X. Jin, J. V. Deshmukh, J.Kapinski,
% K. Ueda, and K. Butts
