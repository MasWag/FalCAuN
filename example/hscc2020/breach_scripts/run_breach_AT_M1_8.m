%% Falsify AT_M1_8 using Breach

InitBreach;
BrAT = BreachSimulinkSystem('Autotrans_shift');
InitAT(BrAT);

STL_ReadFile('../breach_stl/AT_M1_8.stl');

Ss = [AT_M1_8_1, AT_M1_8_2, AT_M1_8_3, AT_M1_8_4, AT_M1_8_5, AT_M1_8_6, ...
      AT_M1_8_7, AT_M1_8_8];

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
