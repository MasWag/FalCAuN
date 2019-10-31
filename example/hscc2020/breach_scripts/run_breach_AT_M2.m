%% Falsify AT_M2 using Breach

InitBreach;
BrAT = BreachSimulinkSystem('Autotrans_shift');
InitAT(BrAT);

STL_ReadFile('../breach_stl/AT_M2.stl');

Ss = [M2_1, M2_2, M2_3, M2_4, M2_5, M2_6, M2_7, M2_8, M2_9, M2_10, M2_11, M2_12];
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
