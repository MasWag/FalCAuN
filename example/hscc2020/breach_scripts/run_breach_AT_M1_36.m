%% Falsify AT_M1_36 using Breach

InitBreach;
BrAT = BreachSimulinkSystem('Autotrans_shift');
InitAT(BrAT);

STL_ReadFile('../breach_stl/AT_M1_36.stl');

Ss = [M1_1, M1_2, M1_3, M1_4, M1_5, M1_6, M1_7, M1_8, M1_9, M1_10, ...
      M1_11, M1_12, M1_13, M1_14, M1_15, M1_16, M1_17, M1_18, M1_19, ...
      M1_20, M1_21, M1_22, M1_23, M1_24, M1_25, M1_26, M1_27, M1_28, ...
      M1_29, M1_30, M1_31, M1_32, M1_33, M1_34, M1_35, M1_36];

numFalsified = 0;

total_time = 0;
for spec = Ss
    BrATSample = BrAT.copy();
    falsif_pb = FalsificationProblem(BrATSample, spec);
    % We use CMA-ES
    falsif_pb.max_time = 900; % give the solver 900 seconds to
                              % falsify the property. This is same
                              % as [Zhang+, EMSOFT'18].
    falsif_pb.max_obj_eval = inf;
    falsif_pb.setup_cmaes()
    tic;
    falsif_pb.solve();
    current_exec_time = toc;
    if falsif_pb.obj_best >= 0
        fprintf("Faled to falsify %s\n", '!!');
    else
        fprintf("Falsified %s\n", '!!');
        total_time = total_time + current_exec_time;
        numFalsified = numFalsified + 1;
    end
end

fprintf("%d specifications are falsified\n", numFalsified);
fprintf("The total time to falsify the falsifiable specifications is: %s [s]\n", total_time);
