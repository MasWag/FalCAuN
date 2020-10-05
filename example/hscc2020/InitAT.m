%% Init Script for the Automatic transmission  model
% We use the automatic transmission model in [Hoxha et al.,
% ARCH@CPSWeek 2014].

%% Load the AT model
mdl = 'Autotrans_shift';
load_system(mdl);

%% References
% * [Hoxha et al., ARCH@CPSWeek 2014]: *Benchmarks for Temporal
% Logic Requirements for Automotive Systems*, ARCH@CPSWeek 2014,
% Bardh Hoxha, Houssam Abbas, Georgios E. Fainekos
