%% Init Script for the Abstract Fuel Control Model
% We use the abstract fuel control model in [Jin et al., HSCC'14].

%% Load the AFC model
mdl = 'AbstractFuelControl';
load_system(mdl);

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