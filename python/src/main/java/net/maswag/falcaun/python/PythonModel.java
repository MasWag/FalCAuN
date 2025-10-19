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
import java.util.NoSuchElementException;

/**
 * A PythonModel class wraps a model implemented by python.
 * The model is expected to have methods {@code pre()}, {@code post()}, {@code step(I inputSignal) -> O}, and {@code close()}.
 * If the model has an {@code exec(List<I> inputSignals) -> List<O>} method,
 * NumericSUL can be used to execute a batch of input signals for optimization.
 * This class uses Jep library to interact with Python.
 * 
 * @param <I> Type of the input at each step
 * @param <O> Type of the output at each step
 */
public class PythonModel<I, O> {
    /**
     * A thread-local variable to check if the interpreter has been initialized.
     */
    private ThreadLocal<Boolean> initialized = ThreadLocal.withInitial(() -> false);

    /**
     * A {@link jep.SharedInterpreter} variable to hold the Python interpreter instance.
     * {@code interpreter} uses ThreadLocal because {@link jep.SharedInterpreter} cannot be used by another thread.
     */
    private ThreadLocal<SharedInterpreter> interpreter = ThreadLocal.withInitial(() -> {
        try {
            return new SharedInterpreter();
        } catch (JepException e) {
            throw new RuntimeException(e);
        }
    });

    /**
     * The class object of the output signal produced by the step method.
     */
    private final Class<O> outputClass;

    /**
     * The filename of the Python script that implements the SUL model.
     */
    private final String initScript;


    /**
     * Objects representing callable Python methods.
     */
    private PyCallable pyPre, pyPost, pyStep, pyClose;

    /**
     * It is bound if the Python model has an {@code exec} method.
     */
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
     * The script should define a class {@code SUL} with methods {@code pre()}, {@code post()}, {@code step(I inputSignal) -> O}, and {@code close()}.
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
     * Calling a callable method like {@literal pyPre.call()} is equivalent to executing
     * {@literal sul = SUL()} and {@literal sul.pre()} on the Python side.
     *
     * Note that the code under the {@literal if __name__ == "__main__":} branch in Python is also executed.
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

    /**
     * Call the {@code pre} method of the Python SUL model.
     * If the model has not been initialized in this thread yet, it initializes first.
     */
    public void pre() {
        initialize();
        this.pyPre.call();
    }

    /**
     * Call the {@code post} method of the Python SUL model.
     */
    public void post() {
        this.pyPost.call();
    }

    /**
     * Call the {@code step} method of the Python SUL model.
     * For the given {@code outputClass}, it converts the output object produced by Python to type {@code O} using Jep.
     *
     * @throws JepException if an error occurs while calling the Python step method.
     */
    public O step(I inputSignal) throws JepException {
        simulationTime.start();
        var ret = this.pyStep.callAs(this.outputClass, inputSignal);
        simulationTime.stop();
        return ret;
    }

    /**
     * Call the {@code close} method of the Python SUL model.
     */
    public void close() {
        this.pyClose.call();
        this.interpreter.get().close();
    }

    /**
     * Returns true if the Python SUL model has {@code exec} method.
     */
    public boolean hasExec() {
        return this.pyExec.isPresent();
    }

    /**
     * Call the {@code exec} method of the Python SUL model.
     * 
     * @throws NoSuchElementException if the Python SUL model does not have {@code exec} method.
     * @throws JepException if an error occurs while calling the Python step method.
     */
    @SuppressWarnings("rawtypes")
    public ArrayList exec(List<I> inputSignals) throws NoSuchElementException, JepException {
        simulationTime.start();
        var ret = this.pyExec.orElseThrow().callAs(ArrayList.class, inputSignals);
        simulationTime.stop();
        return ret;
    }
}
