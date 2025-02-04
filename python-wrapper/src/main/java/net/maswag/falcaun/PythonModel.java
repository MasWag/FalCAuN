package net.maswag.falcaun;

import jep.SharedInterpreter;
import jep.JepException;
import jep.JepConfig;
import jep.python.PyCallable;
import jep.python.PyObject;

import java.util.ArrayList;
import java.util.List;

import lombok.extern.slf4j.Slf4j;

/**
 * Raw Simulink model. We use the fixed step execution of Simulink to make
 * sampling easier.
 */
@Slf4j
public class PythonModel {
    private final SharedInterpreter interpreter;

    private final PyCallable pyPre, pyPost, pyStep, pyClose;

    public PythonModel(String initScript) throws JepException {
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

    public ArrayList<Double> step(List<Double> inputSignal) throws JepException {
        var ret = this.pyStep.callAs(ArrayList.class, inputSignal);
        for (var e : ret) {
            if (!(e instanceof Double)) {
                throw new JepException();
            }
        }
        // var ret = this.pyStep.callAs(ArrayList.class, inputSignal);
        return (ArrayList<Double>) ret;
    }

    public void close() {
        this.pyClose.call();
    }
}
