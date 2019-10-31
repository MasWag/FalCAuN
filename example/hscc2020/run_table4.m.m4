fileID = fopen('./results/table4.matlab.result', 'a');
robustness = try_simulink(BrAT, SPEC, throttles, brakes);
fprintf(fileID, "%s\t%s\n", 'ID', robustness);
fclose(fileID);

