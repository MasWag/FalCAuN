package net.maswag.falcaun;

import jep.JepConfig;
import jep.JepException;
import jep.SharedInterpreter;
import jep.python.PyCallable;
import jep.python.PyObject;

/**
 * A PythonModel class wraps a model implemented by python.
 * The model is expected to have methods pre(), post(), step(I inputSignal) -> O, and close().
 * This class uses Jep library to interact with Python.
 */
public class PythonModel<I, O> {
    /**
     * A thread-local variable to check if the interpreter has been initialized.
     */
    private ThreadLocal<Boolean> initialized = ThreadLocal.withInitial(() -> false);

    /**
     * `interpreter` use ThreadLocal because SharedInterpreter cannot be used by the other thread.
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

    static {
        // JepConfig must be set before creating any SharedInterpreters
        SharedInterpreter.setConfig(new JepConfig().redirectStdout(System.out).redirectStdErr(System.err));
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
        return this.pyStep.callAs(this.outputClass, inputSignal);
    }

    public void close() {
        this.pyClose.call();
        this.interpreter.get().close();
    }
}
