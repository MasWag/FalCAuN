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
