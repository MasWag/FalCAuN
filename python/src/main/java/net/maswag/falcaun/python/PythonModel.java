package net.maswag.falcaun.python;

import jep.JepConfig;
import jep.JepException;
import jep.SharedInterpreter;
import jep.python.PyCallable;
import jep.python.PyObject;
import lombok.Getter;
import net.maswag.falcaun.TimeMeasure;

import java.util.ArrayList;
import java.util.List;
import java.util.NoSuchElementException;
import java.util.Optional;

/**
 * A PythonModel class wraps a model implemented by python.
 * The model is expected to have methods {@code pre()}, {@code post()}, {@code step(I inputSignal) -> O}, and {@code close()}.
 * If the model has an {@code exec(List<I> inputSignals) -> List<O>} method,
 * NumericSUL can be used to execute a batch of input signals for optimization.
 * This class uses Jep library to interact with Python.
 * <p>
 * A {@link SharedInterpreter} can be used only by the thread that created it. Therefore, each thread using this
 * model has its own binding, i.e., an interpreter, an instance of the Python class {@code SUL}, and the callable
 * methods of the instance. The binding of a thread is created when the thread uses the model for the first time.
 * {@link #close()} closes only the binding of the calling thread.
 *
 * @param <I> Type of the input at each step
 * @param <O> Type of the output at each step
 */
public class PythonModel<I, O> {
    /**
     * The per-thread binding of the Python model.
     *
     * @param interpreter the interpreter owned by the thread
     * @param pre         the {@code pre} method of the Python SUL
     * @param post        the {@code post} method of the Python SUL
     * @param step        the {@code step} method of the Python SUL
     * @param close       the {@code close} method of the Python SUL
     * @param exec        the {@code exec} method of the Python SUL if it exists
     */
    private record Binding(SharedInterpreter interpreter, PyCallable pre, PyCallable post, PyCallable step,
                           PyCallable close, Optional<PyCallable> exec) {
    }

    /**
     * The binding of each thread. It is created lazily by {@link #createBinding()}.
     */
    private final ThreadLocal<Binding> binding = ThreadLocal.withInitial(this::createBinding);

    /**
     * The class object of the output signal produced by the step method.
     */
    private final Class<O> outputClass;

    /**
     * The filename of the Python script that implements the SUL model.
     */
    private final String initScript;

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
     * The binding for the current thread is created eagerly so that errors in the script are reported here.
     *
     * @param initScript The Python script to initialize the model.
     * @param outputClass The class object of the output signal produced by the step method.
     * @throws JepException If there is an error initializing the Python interpreter or running the script.
     */
    public PythonModel(String initScript, Class<O> outputClass) throws JepException {
        this.outputClass = outputClass;
        this.initScript = initScript;
        this.binding.get();
    }

    /**
     * Creates the binding for the current thread.
     * It runs the initialization script, executes {@literal sul = SUL()}, and binds the methods of {@literal sul}.
     * <p>
     * Note that the code under the {@literal if __name__ == "__main__":} branch in Python is also executed.
     */
    private Binding createBinding() {
        SharedInterpreter interp;
        try {
            interp = new SharedInterpreter();
        } catch (JepException e) {
            throw new IllegalStateException("Failed to create a Python interpreter", e);
        }
        try {
            interp.runScript(initScript);
            interp.eval("sul = SUL()");

            var pysul = interp.getValue("sul", PyObject.class);
            Object hasExecObj = interp.getValue("hasattr(sul, 'exec')");
            Optional<PyCallable> exec = hasExecObj instanceof Boolean hasExec && hasExec
                    ? Optional.of(pysul.getAttr("exec", PyCallable.class))
                    : Optional.empty();
            return new Binding(interp,
                    pysul.getAttr("pre", PyCallable.class),
                    pysul.getAttr("post", PyCallable.class),
                    pysul.getAttr("step", PyCallable.class),
                    pysul.getAttr("close", PyCallable.class),
                    exec);
        } catch (RuntimeException e) {
            interp.close();
            throw e;
        }
    }

    /**
     * Call the {@code pre} method of the Python SUL model.
     */
    public void pre() {
        binding.get().pre().call();
    }

    /**
     * Call the {@code post} method of the Python SUL model.
     */
    public void post() {
        binding.get().post().call();
    }

    /**
     * Call the {@code step} method of the Python SUL model.
     * For the given {@code outputClass}, it converts the output object produced by Python to type {@code O} using Jep.
     *
     * @throws JepException if an error occurs while calling the Python step method.
     */
    public O step(I inputSignal) throws JepException {
        PyCallable step = binding.get().step();
        simulationTime.start();
        try {
            return step.callAs(this.outputClass, inputSignal);
        } finally {
            simulationTime.stop();
        }
    }

    /**
     * Call the {@code close} method of the Python SUL model and close the interpreter of the current thread.
     * The bindings of the other threads are not closed because an interpreter can be closed only by its thread.
     */
    public void close() {
        Binding current = binding.get();
        try {
            current.close().call();
        } finally {
            current.interpreter().close();
            binding.remove();
        }
    }

    /**
     * Returns true if the Python SUL model has {@code exec} method.
     */
    public boolean hasExec() {
        return binding.get().exec().isPresent();
    }

    /**
     * Call the {@code exec} method of the Python SUL model.
     *
     * @throws NoSuchElementException if the Python SUL model does not have {@code exec} method.
     * @throws JepException if an error occurs while calling the Python step method.
     */
    @SuppressWarnings("rawtypes")
    public ArrayList exec(List<I> inputSignals) throws NoSuchElementException, JepException {
        PyCallable exec = binding.get().exec().orElseThrow();
        simulationTime.start();
        try {
            return exec.callAs(ArrayList.class, inputSignals);
        } finally {
            simulationTime.stop();
        }
    }
}
