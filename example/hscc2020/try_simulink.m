function robustness = try_simulink(BrAT, phi, throttles,brakes)
    assert(length(throttles) == length(brakes));
    len = length(throttles);

    BrATSim = BrAT.copy();
    input_gen.type = 'UniStep';
    input_gen.cp = len;
    BrATSim.SetInputGen(input_gen);

    for i = 1:len
        BrATSim.SetParam({sprintf('throttle_u%d', i - 1)}, throttles(i));
        BrATSim.SetParam({sprintf('brake_u%d', i - 1)}, brakes(i));
    end
    BrATSim.Sim(0:.1:len);
    robustness = BrATSim.CheckSpec(phi);
end

