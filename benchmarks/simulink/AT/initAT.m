%% Init Script for the Automatic transmission (AT) benchmark
% We use the automatic transmission model in [Hoxha et al.,
% ARCH@CPSWeek 2014].
%
% Usage (the absolute path makes MATLAB run exactly this file):
%   run('<FalCAuN>/benchmarks/simulink/AT/initAT.m');
% This script defines `mdl` and the model parameters in the caller's workspace,
% as FalCAuN expects from an initialization script. See ../README.md and
% ../third_party/README.md.

%% Add the example directory to the path
% The model loads sldemo_autotrans_data from the example by MathWorks.
versionString = version('-release');
oldpath = path;
path(strcat(userpath, '/Examples/R', versionString, '/simulink_automotive/ModelingAnAutomaticTransmissionControllerExample/'), oldpath);

%% Load the AT model from the pinned Breach submodule by its absolute path
% A model with the same name elsewhere on the MATLAB path is never used instead.
falcaunBenchmarkDir = fileparts(mfilename('fullpath')); % directory of this script
falcaunPreviousDir = cd(falcaunBenchmarkDir); % resolve '..' and relative paths
falcaunBenchmarkDir = pwd;
cd(falcaunPreviousDir);
modelFile = fullfile(fileparts(falcaunBenchmarkDir), 'third_party', 'breach', 'Ext', 'Models', 'Autotrans_shift.mdl');
if ~isfile(modelFile)
    error('FalCAuN:missingSubmodule', ['Simulink model not found: %s\n' ...
        'Initialize the Git submodules of FalCAuN with: git submodule update --init --recursive'], modelFile);
end
mdl = 'Autotrans_shift';
if bdIsLoaded(mdl) && ~strcmp(get_param(mdl, 'FileName'), modelFile)
    close_system(mdl, 0);
end
load_system(modelFile);
clear falcaunBenchmarkDir falcaunPreviousDir modelFile;

%% Use the data in US customary units, which the model assumes
% Since R2026b, the example by MathWorks provides sldemo_autotrans_data in
% SI units. We convert such data back to US customary units.
hws = get_param(mdl, 'ModelWorkspace');
if max(hws.getVariable('nevec')) < 1000 % rad/s instead of rpm
    lbfft = 1.35582; % N*m per lbf*ft, as used by MathWorks
    rpm = 2 * pi / 60; % rad/s per rpm
    mph = 0.44704; % m/s per mph
    ft = 0.3048; % m per ft
    hws.assignin('nevec', hws.getVariable('nevec') / rpm);
    hws.assignin('emap', hws.getVariable('emap') / lbfft);
    hws.assignin('Iei', hws.getVariable('Iei') / (lbfft / rpm));
    hws.assignin('uptab', hws.getVariable('uptab') / mph);
    hws.assignin('downtab', hws.getVariable('downtab') / mph);
    converterData = hws.getVariable('converter_data');
    converterData(:, 2) = converterData(:, 2) / (rpm / sqrt(lbfft));
    hws.assignin('converter_data', converterData);
    vehicleData = hws.getVariable('vehicledata');
    vehicleData(:) = vehicleData(:) ./ [1; lbfft; lbfft / mph^2; ft; lbfft / rpm; 1];
    hws.assignin('vehicledata', vehicleData);
    clear lbfft rpm mph ft converterData vehicleData;
end
clear hws;

%% References
% * [Hoxha et al., ARCH@CPSWeek 2014]: *Benchmarks for Temporal
% Logic Requirements for Automotive Systems*, ARCH@CPSWeek 2014,
% Bardh Hoxha, Houssam Abbas, Georgios E. Fainekos
