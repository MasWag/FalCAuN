package net.maswag.falcaun;

import jep.JepConfig;
import jep.JepException;
import jep.SharedInterpreter;
import jep.python.PyCallable;
import jep.python.PyObject;

import lombok.extern.slf4j.Slf4j;

/**
 * Raw Simulink model. We use the fixed step execution of Simulink to make
 * sampling easier.
 */
@Slf4j
public class PythonModel<I, O> {
    private final SharedInterpreter interpreter;

    private final PyCallable pyPre, pyPost, pyStep, pyClose;
    private final Class<O> outputClass;
    public PythonModel(String initScript, Class<O> outputClass) throws JepException {
        this.outputClass = outputClass;
        SharedInterpreter.setConfig(new JepConfig().redirectStdout(System.out).redirectStdErr(System.err));
        this.interpreter = new SharedInterpreter();

        this.interpreter.runScript(initScript);
        // this.interpreter.eval(String.format("import %s as s", moduleName));
        this.interpreter.eval("sul = SUL()");
        var pysul = this.interpreter.getValue("sul", PyObject.class);

        this.pyPre = pysul.getAttr("pre", PyCallable.class);
        this.pyPost = pysul.getAttr("post", PyCallable.class);
        this.pyStep = pysul.getAttr("step", PyCallable.class);
        this.pyClose = pysul.getAttr("close", PyCallable.class);
    }

    public void pre() {
        this.pyPre.call();
    }

    public void post() {
        this.pyPost.call();
    }

    public O step(I inputSignal) throws JepException {
        //Type ty = getClass().getGenericSuperclass();
        //var clazz = ((Class<O>)((ParameterizedType)ty).getActualTypeArguments()[1]);
        return this.pyStep.callAs(this.outputClass, inputSignal);
    }

    public void close() {
        this.pyClose.call();
    }
}
