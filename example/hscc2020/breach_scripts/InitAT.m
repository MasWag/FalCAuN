%% Initialize the automatic transmission model
function InitAT( BrAT )

%% Describes and generate driving scenarios
% We create an input generator that will alternates between acceleration and braking

BrAT.Sys.tspan =0:.01:30;
input_gen.type = 'UniStep';
input_gen.cp = 30;
BrAT.SetInputGen(input_gen);

for cpi = 0:input_gen.cp -1
    throttle_sig = strcat('throttle_u',num2str(cpi));
    BrAT.SetParamRanges({throttle_sig},[0.0 100.0]);
    brake_sig = strcat('brake_u',num2str(cpi));
    BrAT.SetParamRanges({brake_sig},[0.0 325.0]);
end

% define the input parameters and ranges
% input_params.names = {'throttle_u0'};
% input_params.ranges = [0 100];

AT_Falsify = BrAT.copy();
end

