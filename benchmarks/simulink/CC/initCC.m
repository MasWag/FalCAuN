%% Init Script for the Chasing Cars (CC) benchmark
% We use the chasing cars model in [Hoxha et al., ARCH@CPSWeek 2014],
% as provided by https://github.com/lassekotz/Chasing_Cars.
%
% Usage (the absolute path makes MATLAB run exactly this file):
%   run('<FalCAuN>/benchmarks/simulink/CC/initCC.m');
% This script defines `mdl` and the model parameters in the caller's workspace,
% as FalCAuN expects from an initialization script. See ../README.md and
% ../third_party/README.md.

%% Load the CC model from the pinned Chasing Cars submodule by its absolute path
% A model with the same name elsewhere on the MATLAB path is never used instead.
falcaunBenchmarkDir = fileparts(mfilename('fullpath')); % directory of this script
falcaunPreviousDir = cd(falcaunBenchmarkDir); % resolve '..' and relative paths
falcaunBenchmarkDir = pwd;
cd(falcaunPreviousDir);
modelFile = fullfile(fileparts(falcaunBenchmarkDir), 'third_party', 'chasing_cars', 'cars.mdl');
if ~isfile(modelFile)
    error('FalCAuN:missingSubmodule', ['Simulink model not found: %s\n' ...
        'Initialize the Git submodules of FalCAuN with: git submodule update --init --recursive'], modelFile);
end
mdl = 'cars';
if bdIsLoaded(mdl) && ~strcmp(get_param(mdl, 'FileName'), modelFile)
    close_system(mdl, 0);
end
load_system(modelFile);
clear falcaunBenchmarkDir falcaunPreviousDir modelFile;
