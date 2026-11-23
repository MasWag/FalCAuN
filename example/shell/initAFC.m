%% Init Script for the Abstract Fuel Control (AFC) benchmark
% This is a thin wrapper of the shared FalCAuN benchmark definition
% benchmarks/simulink/AFC/initAFC.m, which loads the model from a pinned Git submodule.
% See benchmarks/simulink/README.md.
falcaunRoot = fileparts(mfilename('fullpath')); % directory of this script
for falcaunLevel = 1:2 % up to the root of the FalCAuN repository
    falcaunRoot = fileparts(falcaunRoot);
end
falcaunInitScript = fullfile(falcaunRoot, 'benchmarks', 'simulink', 'AFC', 'initAFC.m');
clear falcaunRoot falcaunLevel;
run(falcaunInitScript);
clear falcaunInitScript;

%% Wrap the model for Breach (Breach must be on the MATLAB path)
warning('off', 'Simulink:LoadSave:EncodingMismatch')
BrMdl = BreachSimulinkSystem(mdl);
