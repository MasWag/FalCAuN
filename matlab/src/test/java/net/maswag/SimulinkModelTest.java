package net.maswag;

import com.mathworks.engine.EngineException;
import net.automatalib.word.Word;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.List;
import java.util.concurrent.ExecutionException;


class SimulinkModelTest {
    private SimulinkModel mdl;
    private final String PWD = System.getenv("PWD");
    private final String initScript = "cd " + PWD + "/src/test/resources/MATLAB; initAFC;";
    private final Double signalStep = 2.0;

    @BeforeEach
    void setUp() throws ExecutionException, InterruptedException {
        this.mdl = new SimulinkModel(initScript,
                Arrays.asList("Pedal Angle", "Engine Speed"),
                signalStep, 0.0025);
        this.mdl.setSimulationStep(0.0001);
    }

    @AfterEach
    void tearDown() throws EngineException {
        this.mdl.close();
    }

    @Test
    void execute() throws ExecutionException, InterruptedException {
        // Give [80.0, 900.0] by repeating 10 times
        List<List<Double>> input = Arrays.asList(
                Arrays.asList(80.0, 900.0),
                Arrays.asList(80.0, 900.0),
                Arrays.asList(80.0, 900.0),
                Arrays.asList(80.0, 900.0),
                Arrays.asList(80.0, 900.0),
                Arrays.asList(80.0, 900.0),
                Arrays.asList(80.0, 900.0),
                Arrays.asList(80.0, 900.0),
                Arrays.asList(80.0, 900.0),
                Arrays.asList(80.0, 900.0));
        ValueWithTime<List<Double>> result = this.mdl.execute(Word.fromList(input));
        // Test that the first time stamp is 0.0
        Assertions.assertEquals(0.0, result.getTimestamps().get(0).doubleValue());
        // Test that the last time stamp is 18.0
        Assertions.assertEquals(18.0, result.getTimestamps().get(result.getTimestamps().size() - 1).doubleValue());
    }

    @Test
    void step() {
        double lastTime = Double.NEGATIVE_INFINITY; // The dummy value for the first case
        // Give [80.0, 900.0] for 10 times
        List<Double> input = Arrays.asList(80.0, 900.0);
        for (int i = 0; i < 10; i++) {
            ValueWithTime<List<Double>> result = this.mdl.step(input);
            if (lastTime < 0.0) {
                // The result only contains the information at time 0
                Assertions.assertEquals(1, result.getTimestamps().size());
                Assertions.assertEquals(0.0, result.getTimestamps().get(0));
            } else {
                // Test that the first time stamp is always 0
                Assertions.assertEquals(0.0, result.getTimestamps().get(0));
                // Test that the last time stamp is 2.0 larger than the latest last time stamp
                Assertions.assertEquals(result.getTimestamps().get(result.getTimestamps().size() - 1), lastTime + signalStep);
            }
            lastTime = result.getTimestamps().get(result.getTimestamps().size() - 1);
        }
        // Since the total number of steps is 10, the last time stamp should be 18.0
        Assertions.assertEquals(this.signalStep * 9, lastTime);
    }
}