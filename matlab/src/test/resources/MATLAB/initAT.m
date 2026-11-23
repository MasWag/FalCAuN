%% Init Script for the Automatic transmission (AT) benchmark
% This is a thin wrapper of the shared FalCAuN benchmark definition
% benchmarks/simulink/AT/initAT.m, which loads the model from a pinned Git submodule.
% See benchmarks/simulink/README.md.
falcaunRoot = fileparts(mfilename('fullpath')); % directory of this script
for falcaunLevel = 1:5 % up to the root of the FalCAuN repository
    falcaunRoot = fileparts(falcaunRoot);
end
falcaunInitScript = fullfile(falcaunRoot, 'benchmarks', 'simulink', 'AT', 'initAT.m');
clear falcaunRoot falcaunLevel;
run(falcaunInitScript);
clear falcaunInitScript;
