package net.maswag.falcaun.simulink;

import com.mathworks.engine.EngineException;
import com.mathworks.engine.MatlabEngine;
import de.learnlib.exception.SULException;
import lombok.Getter;
import lombok.Setter;
import lombok.extern.slf4j.Slf4j;
import net.automatalib.word.Word;
import net.maswag.falcaun.Signal;
import net.maswag.falcaun.TimeMeasure;
import net.maswag.falcaun.ValueWithTime;

import org.apache.commons.lang3.ArrayUtils;
import org.jetbrains.annotations.NotNull;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Stream;
import java.util.concurrent.ExecutionException;

/**
 * Raw Simulink model. We use the fixed step execution of Simulink to make sampling easier.
 */
@Slf4j
public class SimulinkModel {
    /**
     * The signal step of the input signal.
     */
    @Getter
    private final Double signalStep;
    /**
     * The simulation step of Simulink.
     * <p>
     * If this value is too large, Simulink can abort due to a computation error. In that case, you should make this value larger.
     */
    @Getter
    private double simulinkSimulationStep;
    private final MatlabEngine matlab;
    private final LockedMatlabEngine lockedEngine;
    private final Path cacheDir;
    private final Path codegenDir;
    private final Path workingDir;
    private final List<String> paramNames;
    /**
     * The current time of the simulation
     */
    public double getCurrentTime() {
        return inputSignal.duration();
    }
    private Signal inputSignal;
    private boolean isInitial = true;
    private boolean useFastRestart = true;
    @Getter
    private int counter = 0;
    private final TimeMeasure simulationTime = new TimeMeasure();
    @Setter
    private InterpolationMethod interpolationMethod = InterpolationMethod.LINEAR;

    /**
     * Setter of simulinkSimulationStep
     *
     * @param simulinkSimulationStep The fixed simulation step of Simulink. If this value is too large, Simulink can abort due to an computation error.
     */
    public void setSimulationStep(double simulinkSimulationStep) {
        this.simulinkSimulationStep = simulinkSimulationStep;
    }

    public SimulinkModel(String initScript, List<String> paramNames, Double signalStep, Double simulinkSimulationStep) throws InterruptedException, ExecutionException {
        // Load System here
        this.paramNames = paramNames;
        this.signalStep = signalStep;
        this.simulinkSimulationStep = simulinkSimulationStep;
        this.lockedEngine = MatlabEngineManager.acquireEngine();
        this.matlab = this.lockedEngine.engine();

        Path cacheDirTmp;
        Path codegenDirTmp;
        Path workingDirTmp;
        try {
            cacheDirTmp = Files.createTempDirectory("falcaun-sl-cache");
            codegenDirTmp = Files.createTempDirectory("falcaun-sl-codegen");
            workingDirTmp = Files.createTempDirectory("falcaun-sl-work");
            matlab.putVariable("falcaunCacheDir", cacheDirTmp.toString());
            matlab.putVariable("falcaunCodegenDir", codegenDirTmp.toString());
            matlab.eval("Simulink.fileGenControl('set', 'CacheFolder', falcaunCacheDir, 'CodeGenFolder', falcaunCodegenDir);");
            matlab.eval("clear falcaunCacheDir falcaunCodegenDir;");
        } catch (IOException e) {
            throw new ExecutionException("Failed to prepare Simulink file generation folders", e);
        }

        cacheDir = cacheDirTmp;
        codegenDir = codegenDirTmp;
        workingDir = workingDirTmp;

        matlab.eval("clear;");
        cleanupMatlabSession();
        matlab.eval("warning('off', 'Simulink:LoadSave:EncodingMismatch')");
        matlab.putVariable("signalStep", signalStep);
        String resourceDir = extractResourceDirectory(initScript);
        try {
            matlab.eval(initScript);
        } catch (Exception e) {
            log.error("An error occurred during running the initial script. This also happens if the engine is not correctly installed.");
            log.error("Init Script: {}", initScript);
            throw e;
        }

        if (resourceDir != null) {
            matlab.putVariable("falcaunModelDir", resourceDir);
            matlab.eval("addpath(falcaunModelDir);");
            matlab.eval("clear falcaunModelDir;");
        }

        matlab.putVariable("falcaunWorkingDir", workingDir.toString());
        matlab.eval("cd(falcaunWorkingDir);");
        matlab.eval("clear falcaunWorkingDir;");
        // Initialize the current state
        this.reset();
    }

    /**
     * Reset the Simulink model to the initial state.
     */
    public void reset() {
        inputSignal = new Signal(signalStep);
        isInitial = true;
    }

    /**
     * Clear the counter and the time measure.
     */
    public void clear() {
        counter = 0;
        simulationTime.reset();
    }

    /**
     * Advance the logical SUL state by one input symbol.
     * <p>
     * The Java-side input prefix is extended with {@code inputSignal}. The current low-level implementation then
     * replays the whole accumulated prefix from the Simulink model's initial state, because this has been faster than
     * loading and saving Simulink final states for the workloads covered by the tests. Thus this method is incremental
     * from the caller's SUL perspective, but the raw trace returned by this method may contain the whole replayed prefix
     * and start at time {@code 0.0}.
     *
     * @param inputSignal The next input symbol
     * @return The output signal with timestamps of the replayed prefix.
     */
    @NotNull
    public ValueWithTime<List<Double>> step(@NotNull List<Double> inputSignal) {
        if (this.isInitial) {
            counter++;
        }
        assert isInitial || !inputSignal.isEmpty();
        log.trace("Input: {}", inputSignal);

        this.inputSignal.add(inputSignal);
        List<List<Double>> result = new ArrayList<>();
        List<Double> timestamps;
        // For efficiency, we use StringBuilder to make the entire script to execute in MATLAB rather than evaluate each line.
        StringBuilder builder = new StringBuilder();
        try {
            isInitial = false;

            SimulationTrace trace = runReplaySimulationWithRetry(builder, this.inputSignal.duration());
            double[][] y = trace.y;
            double[] t = trace.t;

            // convert double[][] to List<List<Double>>
            for (double[] outputStep: y) {
                result.add(Arrays.asList(ArrayUtils.toObject(outputStep)));
            }

            // convert double[] to List<Double>
            timestamps = Arrays.asList(ArrayUtils.toObject(t));
        } catch (Exception e) {
            log.error("There was an error in the simulation: {}", e.getMessage());
            log.error("The executed script was: {}", builder);
            assert false;
            throw new SULException(e);
        }

        // Final internal process
        assert !isInitial;
        log.trace("Output: {}", result);

        return new ValueWithTime<>(timestamps, result);
    }

    private void makeDataSet(StringBuilder builder) throws ExecutionException, InterruptedException {
        builder.append("timeVector = ").append(inputSignal.getTimestamps()).append(";");
        builder.append("ds = Simulink.SimulationData.Dataset;");
        for (int i = 0; i < inputSignal.dimension(); i++) {
            double[] tmp = inputSignal.dimensionGet(i).stream().mapToDouble(Double::doubleValue).toArray();
            matlab.putVariable("tmp" + i, tmp);
            builder.append("input").append(i).append(" = timeseries(tmp").append(i).append(", timeVector);");
            if (this.interpolationMethod == InterpolationMethod.CONSTANT) {
                // Set the interpolation method to zoh https://jp.mathworks.com/help/matlab/ref/timeseries.setinterpmethod.html
                //builder.append("input").append(i).append(" = setinterpmethod(input").append(i).append(", 'zoh');");
                builder.append("input").append(i).append(".DataInfo.Interpolation = tsdata.interpolation('zoh');");
            } else {
                // Set the interpolation method to linear https://jp.mathworks.com/help/matlab/ref/timeseries.setinterpmethod.html
                //builder.append("input").append(i).append(" = setinterpmethod(input").append(i).append(", 'linear');");
                builder.append("input").append(i).append(".DataInfo.Interpolation = tsdata.interpolation('linear');");
            }
            builder.append("ds = ds.addElement(input").append(i).append(", '").append(paramNames.get(i)).append("');");
        }
    }

    private void configureSimulink(StringBuilder builder) {
        // We use the data in ds
        builder.append("set_param(mdl, 'LoadExternalInput', 'on');");
        builder.append("set_param(mdl, 'ExternalInput', 'ds');");

        // Enable fast restart
        if (this.useFastRestart) {
            builder.append("set_param(mdl,'FastRestart','on');");
        } else {
            builder.append("set_param(mdl,'FastRestart','off');");
        }

        /// Configuration on the accelerator
        // Use normal mode
        // builder.append("set_param(mdl,'SimulationMode','normal');");
        // Enable accelerator mode
        builder.append("set_param(mdl,'SimulationMode','accelerator');");
        // Enable classic accelerator mode
        builder.append("set_param(0, 'GlobalUseClassicAccelMode', 'on');");


        // The save format must be an array
        builder.append("set_param(mdl, 'SaveFormat', 'Array');");
        // We save the output as yout
        builder.append("set_param(mdl, 'SaveOutput', 'on');");
        builder.append("set_param(mdl, 'OutputSaveName', 'yout');");
        // We save the time as tout
        builder.append("set_param(mdl, 'SaveTime', 'on');");
        builder.append("set_param(mdl, 'TimeSaveName', 'tout');");

        // Configuration on the decimation
        builder.append("set_param(mdl, 'SolverType', 'Fixed-step');");
        builder.append("set_param(mdl, 'FixedStep', '").append(simulinkSimulationStep).append("');");
        // We dump all the results
        builder.append("set_param(mdl, 'LimitDataPoints', 'off');");
        // We do not decimate the result
        // builder.append("set_param(mdl, 'Decimation', '").append(signalStep / simulinkSimulationStep).append("');");
    }

    private void preventHugeTempFile(StringBuilder builder) {
        builder.append("Simulink.sdi.setAutoArchiveMode(false);");
        builder.append("Simulink.sdi.setArchiveRunLimit(0);");
        builder.append("Simulink.sdi.clear;");
    }

    private void runSimulation(StringBuilder builder, double startTime, double stopTime, boolean loadInitialState, boolean saveFinalState) {
        // append the input signal
        builder.append("in = Simulink.SimulationInput(mdl);");
        builder.append("in = in.setExternalInput(ds);");

        // Set the StartTime and StopTime
        if (startTime != 0.0) {
            builder.append("in = in.setModelParameter('StartTime', '").append(startTime).append("');");
        }
        builder.append("in = in.setModelParameter('StopTime', '").append(stopTime).append("');");
        // Save the output to yout
        if (!this.useFastRestart) {
            builder.append("in = in.setModelParameter('SaveOutput', 'on');");
            builder.append("in = in.setModelParameter('OutputSaveName', 'yout');");
            builder.append("in = in.setModelParameter('SaveTime', 'on');");
            builder.append("in = in.setModelParameter('TimeSaveName', 'tout');");
        }
        // State loading/saving is supported here, but the default SUL step strategy disables both and replays the
        // accumulated prefix because that is currently the faster behaviorally equivalent implementation.
        if (loadInitialState) {
            builder.append("in = in.setModelParameter('LoadInitialState', 'on');");
            builder.append("in = in.setModelParameter('InitialState', 'myOperPoint');");
        } else {
            builder.append("in = in.setModelParameter('LoadInitialState', 'off');");
        }
        if (saveFinalState) {
            builder.append("in = in.setModelParameter('SaveFinalState', 'on');");
            builder.append("in = in.setModelParameter('FinalStateName', 'myOperPoint');");
            builder.append("in = in.setModelParameter('SaveCompleteFinalSimState', 'on');");
        }

        // Execute the simulation
        builder.append("simOut = sim(in);");
        if (saveFinalState) {
            builder.append("myOperPoint = simOut.get('myOperPoint');");
        }
        // We handle the output as double.
        builder.append("y = double(simOut.get('yout'));");
        builder.append("t = reshape(double(simOut.get('tout')), 1, []);");
    }

    protected double[][] getResult() throws ExecutionException, InterruptedException {
        double[][] y;
        try {
            matlab.eval("ySize = size(y);");
            double[] ySize = matlab.getVariable("ySize");
            if (this.inputSignal.duration() == 0.0) {
                double[] tmpY;
                if (ySize[1] == 1.0) {
                    // When the output is one dimensional, we need to convert it to 1D array first.
                    double tmp = matlab.getVariable("y");
                    tmpY = new double[]{tmp};
                } else {
                    tmpY = matlab.getVariable("y");
                }
                if (Objects.isNull(tmpY)) {
                    log.error("The simulation output is null");
                    y = null;
                } else {
                    y = new double[][]{tmpY};
                }
            } else {
                if (ySize[1] == 1.0) {
                    // When the output is one dimensional, we need to convert it to 2D array.
                    double[] tmpY = matlab.getVariable("y");
                    y = Arrays.stream(tmpY).mapToObj(d -> new double[]{d}).toArray(double[][]::new);
                } else {
                    y = matlab.getVariable("y");
                }
            }
        } catch (Exception e) {
            log.error("There was an error when obtaining the result: {}", e.getMessage());
            throw e;
        }
        return y;
    }

    protected double[] getTimestamps() throws ExecutionException, InterruptedException {
        double[] t;
        try {
            if (this.inputSignal.duration() == 0.0) {
                t = new double[]{0.0};
            } else {
                t = matlab.getVariable("t");
            }
        } catch (Exception e) {
            log.error("There was an error when obtaining the timestamps: {}", e.getMessage());
            throw e;
        }
        return t;
    }

    private String validateTimestamps(double[] timestamps, double expectedStopTime) {
        if (timestamps == null || timestamps.length == 0) {
            return "The simulation timestamps are null or empty";
        }
        double tolerance = Math.max(1.0e-8, simulinkSimulationStep * 10.0);
        double previous = Double.NEGATIVE_INFINITY;
        for (double timestamp : timestamps) {
            if (!Double.isFinite(timestamp) || timestamp < previous - tolerance) {
                return "The simulation timestamps are non-finite or non-monotonic";
            }
            previous = timestamp;
        }
        if (Math.abs(timestamps[0]) > tolerance) {
            return "The simulation does not start at time 0 within tolerance " + tolerance;
        }
        if (Math.abs(timestamps[timestamps.length - 1] - expectedStopTime) > tolerance) {
            return "The simulation does not end at the expected stop time within tolerance " + tolerance;
        }
        return null;
    }

    /**
     * Execute the Simulink model by feeding inputSignal
     * <p>
     * For inputSignal = a1, a2, ..., an, we construct a timed word w = (a1, 0), (a2, T), (a3, 2 * T), ... (an, (n - 1) * T) and execute the Simulink model by feeding the piecewise-linear interpolation of w.
     *
     * @param inputSignal The input signal
     * @return The output signal. The size is same as the input.
     */
    public ValueWithTime<List<Double>> execute(Word<List<Double>> inputSignal) throws InterruptedException, ExecutionException {
        if (this.isInitial) {
            counter++;
        }
        assert isInitial || !inputSignal.isEmpty();
        if (inputSignal == null) {
            return null;
        }
        reset();
        this.inputSignal.addAll(inputSignal);

        // For efficiency, we use StringBuilder to make the entire script to execute in MATLAB rather than evaluate each line.
        StringBuilder builder = new StringBuilder();

        SimulationTrace trace = runReplaySimulationWithRetry(builder, this.inputSignal.duration());
        double[][] y = trace.y;
        double[] t = trace.t;

        // convert double[][] to List<List<Double>>
        List<List<Double>> result = new ArrayList<>();
        for (double[] outputStep: y) {
            result.add(Arrays.asList(ArrayUtils.toObject(outputStep)));
        }

        reset();
        return new ValueWithTime<>(Arrays.asList(ArrayUtils.toObject(t)), result);
    }

    private SimulationTrace runReplaySimulationWithRetry(StringBuilder builder, double expectedStopTime)
            throws ExecutionException, InterruptedException {
        buildReplaySimulationScript(builder, expectedStopTime);
        try {
            runMatlabScript(builder);
            return getValidatedTrace(expectedStopTime);
        } catch (IllegalStateException e) {
            log.warn("Retrying Simulink replay without fast restart after invalid trace: {}", e.getMessage());
            cleanupMatlabSession();
            boolean previousUseFastRestart = this.useFastRestart;
            this.useFastRestart = false;
            StringBuilder retryBuilder = new StringBuilder();
            try {
                buildReplaySimulationScript(retryBuilder, expectedStopTime);
                runMatlabScript(retryBuilder);
                return getValidatedTrace(expectedStopTime);
            } finally {
                this.useFastRestart = previousUseFastRestart;
            }
        }
    }

    private void buildReplaySimulationScript(StringBuilder builder, double expectedStopTime)
            throws ExecutionException, InterruptedException {
        makeDataSet(builder);
        configureSimulink(builder);
        preventHugeTempFile(builder);
        builder.append("set_param(mdl,'SaveFinalState','off');");
        builder.append("set_param(mdl,'LoadInitialState','off');");
        runSimulation(builder, 0.0, expectedStopTime, false, false);
    }

    private void runMatlabScript(StringBuilder builder) throws ExecutionException, InterruptedException {
        simulationTime.start();
        log.trace(builder.toString());
        try {
            matlab.eval(builder.toString());
        } finally {
            simulationTime.stop();
        }
    }

    private SimulationTrace getValidatedTrace(double expectedStopTime) throws ExecutionException, InterruptedException {
        double[][] y = this.getResult();
        double[] t = this.getTimestamps();
        String validationError = validateTrace(y, t, expectedStopTime);
        if (validationError != null) {
            throw new IllegalStateException(validationError);
        }
        return new SimulationTrace(y, t);
    }

    private String validateTrace(double[][] y, double[] timestamps, double expectedStopTime) {
        if (y == null) {
            return "The simulation output is null";
        }
        if (y.length == 0) {
            return "The simulation output is empty";
        }
        if (y[0] == null) {
            return "The first simulation output row is null";
        }
        if (timestamps == null) {
            return "The simulation timestamps are null; output length=" + y.length;
        }
        if (timestamps.length == 0) {
            return "The simulation timestamps are empty; output length=" + y.length;
        }
        if (y.length != timestamps.length) {
            return "The simulation output/timestamp lengths differ: output length=" + y.length
                    + ", timestamp length=" + timestamps.length
                    + ", first timestamp=" + timestamps[0]
                    + ", last timestamp=" + timestamps[timestamps.length - 1]
                    + ", expected stop time=" + expectedStopTime;
        }
        String timestampError = validateTimestamps(timestamps, expectedStopTime);
        if (timestampError != null) {
            return timestampError + "; output length=" + y.length
                    + ", timestamp length=" + timestamps.length
                    + ", first timestamp=" + timestamps[0]
                    + ", last timestamp=" + timestamps[timestamps.length - 1]
                    + ", expected stop time=" + expectedStopTime;
        }
        return null;
    }

    private static final class SimulationTrace {
        private final double[][] y;
        private final double[] t;

        private SimulationTrace(double[][] y, double[] t) {
            this.y = y;
            this.t = t;
        }
    }

    /**
     * Close the MATLAB engine. This method must be called when the object is no longer used.
     */
    public void close() throws EngineException {
        cleanupMatlabSession();
        resetMatlabWorkingDirectory();
        try {
            if (lockedEngine != null) {
                lockedEngine.close();
            }
        } catch (EngineException e) {
            log.error("Failed to release locked MATLAB engine: {}", e.getMessage());
            throw e;
        } finally {
            deleteDirectorySilently(cacheDir);
            deleteDirectorySilently(codegenDir);
            deleteDirectorySilently(workingDir);
        }
    }

    private void resetMatlabWorkingDirectory() {
        try {
            matlab.eval("try; cd(tempdir); catch; end;");
        } catch (Exception e) {
            log.debug("Failed to reset MATLAB working directory", e);
        }
    }

    private void cleanupMatlabSession() {
        try {
            matlab.eval("try; if exist('mdl','var'); set_param(mdl,'FastRestart','off'); end; catch; end;");
            matlab.eval("try; Simulink.sdi.clear; catch; end;");
            matlab.eval("try; clear ds y t ySize simOut myOperPoint timeVector; catch; end;");
        } catch (Exception e) {
            log.debug("Failed to clean up MATLAB/Simulink session", e);
        }
    }

    public static void clearSimulinkBuildArtifacts(Path baseDirectory) {
        if (baseDirectory == null || !Files.exists(baseDirectory)) {
            return;
        }
        List<Path> targets = new ArrayList<>();
        try (Stream<Path> walk = Files.walk(baseDirectory)) {
            walk.forEach(path -> {
                Path fileName = path.getFileName();
                if (fileName == null) {
                    return;
                }
                String name = fileName.toString();
                if (Files.isDirectory(path) && "slprj".equals(name)) {
                    targets.add(path);
                } else if (Files.isRegularFile(path) && isSimulinkArtifact(name)) {
                    targets.add(path);
                }
            });
        } catch (IOException e) {
            throw new IllegalStateException("Failed to inspect Simulink artifacts under " + baseDirectory, e);
        }

        for (Path target : targets) {
            if (Files.isDirectory(target)) {
                deleteDirectorySilently(target);
            } else {
                try {
                    Files.deleteIfExists(target);
                } catch (IOException e) {
                    throw new IllegalStateException("Failed to delete Simulink artifact " + target, e);
                }
            }
        }
    }

    private static boolean isSimulinkArtifact(String name) {
        return name.endsWith(".slxc")
                || name.endsWith(".autosave")
                || name.contains("_acc.mex")
                || name.endsWith(".mexmaca64")
                || name.endsWith(".mexglnxa64")
                || name.endsWith(".mexw64");
    }

    private static void deleteDirectorySilently(Path dir) {
        if (dir == null || !Files.exists(dir)) {
            return;
        }
        try {
            Files.walk(dir)
                    .sorted(Comparator.reverseOrder())
                    .forEach(path -> {
                        try {
                            Files.deleteIfExists(path);
                        } catch (IOException e) {
                            // ignore cleanup errors
                        }
                    });
        } catch (IOException ignored) {
            // ignore cleanup errors
        }
    }

    private static String extractResourceDirectory(String initScript) {
        if (initScript == null) {
            return null;
        }
        int cdIdx = initScript.indexOf("cd");
        if (cdIdx < 0) {
            return null;
        }
        int len = initScript.length();
        int start = cdIdx + 2;
        while (start < len && Character.isWhitespace(initScript.charAt(start))) {
            start++;
        }
        if (start >= len) {
            return null;
        }
        char quote = 0;
        char ch = initScript.charAt(start);
        if (ch == '\'' || ch == '"') {
            quote = ch;
            start++;
        }
        int end = start;
        while (end < len) {
            char current = initScript.charAt(end);
            if (quote != 0) {
                if (current == quote) {
                    break;
                }
            } else if (current == ';') {
                break;
            }
            end++;
        }
        if (end <= start) {
            return null;
        }
        String dir = initScript.substring(start, end).trim();
        return dir.isEmpty() ? null : dir;
    }

    public double getSimulationTimeSecond() {
        return this.simulationTime.getSecond();
    }

    /**
     * Enum for the interpolation methods of the input signal
     */
    public enum InterpolationMethod {
        /**
         * Piecewise constant interpolation
         * Note: This is not supported in the current version.
         */
        CONSTANT,
        /**
         * Piecewise linear interpolation
         */
        LINEAR
    }
}
