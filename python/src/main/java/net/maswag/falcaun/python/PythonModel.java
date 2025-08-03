package net.maswag.falcaun.python;

import jep.JepConfig;
import jep.JepException;
import jep.SharedInterpreter;
import jep.python.PyCallable;
import jep.python.PyObject;
import lombok.Getter;
import net.maswag.falcaun.TimeMeasure;

import java.util.Optional;
import java.util.ArrayList;
import java.util.List;

/**
 * A PythonModel class wraps a model implemented by python.
 * The model is expected to have methods pre(), post(), step(I inputSignal) -> O, and close().
 * If the model has an exec(List<I> inputSignals) -> List<O> method,
 * NumericSUL can be used to execute a batch of input signals for optimization.
 * This class uses Jep library to interact with Python.
 */
public class PythonModel<I, O> {
    /**
     * A thread-local variable to check if the interpreter has been initialized.
     */
    private ThreadLocal<Boolean> initialized = ThreadLocal.withInitial(() -> false);

    /**
     * A {@link jep.SharedInterpreter} variable to hold the Python interpreter instance.
     * {@code interpreter} use ThreadLocal because {@link jep.SharedInterpreter} cannot be used by the other thread.
     */
    private ThreadLocal<SharedInterpreter> interpreter = ThreadLocal.withInitial(() -> {
        try {
            return new SharedInterpreter();
        } catch (JepException e) {
            throw new RuntimeException(e);
        }
    });
    private final Class<O> outputClass;
    private final String initScript;

    private PyCallable pyPre, pyPost, pyStep, pyClose;
    private Optional<PyCallable> pyExec = Optional.empty();

    @Getter
    private final TimeMeasure simulationTime = new TimeMeasure();

    static {
        // JepConfig must be set before creating any SharedInterpreters
        var config = new JepConfig().redirectStdout(System.out)
                                    .redirectStdErr(System.err)
        // Explicitly set the Python path to include the module in the same directory
        // for abstract_sul.py using kotlin examples
                                    .addIncludePaths("./");
        SharedInterpreter.setConfig(config);
        
    }

    /**
     * Constructs a Python interpreter with the given initialization script as a Python model.
     * The script should define a class SUL with methods pre(), post(), step(I inputSignal) -> O, and close().
     * 
     * @param initScript The Python script to initialize the model.
     * @param outputClass The class object of the output signal produced by the step method.
     * @throws JepException If there is an error initializing the Python interpreter or running the script.
     */
    public PythonModel(String initScript, Class<O> outputClass) throws JepException {
        this.outputClass = outputClass;
        this.initScript = initScript;
        initialize();
    }

    /**
     * It simply runs the initialization script and sets up the Python callable methods.
     * Calling them is equivalent to executing `sul = SUL()` and `sul.method()` on the Python side.
     * 
     * Note that the code under `if __name__ == "__main__":` is executed
     */
    public void initialize() {
        if (!this.initialized.get()) {
            var interp = this.interpreter.get();
            interp.runScript(initScript);
            interp.eval("sul = SUL()");

            var pysul = interp.getValue("sul", PyObject.class);
            this.pyPre = pysul.getAttr("pre", PyCallable.class);
            this.pyPost = pysul.getAttr("post", PyCallable.class);
            this.pyStep = pysul.getAttr("step", PyCallable.class);
            this.pyClose = pysul.getAttr("close", PyCallable.class);

            Object hasExecObj = interp.getValue("hasattr(sul, 'exec')");
            // If 'sul' has 'exec' method, bind it to pyExec
            if (hasExecObj instanceof Boolean hasExec && hasExec) {
                this.pyExec = Optional.of(pysul.getAttr("exec", PyCallable.class));
            } else {
                this.pyExec = Optional.empty();
            }
        }
        this.initialized.set(true);
    }

    public void pre() {
        initialize();
        this.pyPre.call();
    }

    public void post() {
        this.pyPost.call();
    }

    /**
     * For the given outputClass, it tries to convert the output object by python to O type by Jep.
     */
    public O step(I inputSignal) throws JepException {
        simulationTime.start();
        var ret = this.pyStep.callAs(this.outputClass, inputSignal);
        simulationTime.stop();
        return ret;
    }

    public void close() {
        this.pyClose.call();
        this.interpreter.get().close();
    }

    public boolean hasExec() {
        return this.pyExec.isPresent();
    }

    @SuppressWarnings("rawtypes")
    public ArrayList exec(List<I> inputSignals) {
        simulationTime.start();
        var ret = this.pyExec.orElseThrow().callAs(ArrayList.class, inputSignals);
        simulationTime.stop();
        return ret;
    }
}
