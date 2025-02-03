package net.maswag.falcaun;

import jep.SharedInterpreter;
import jep.JepException;
import jep.JepConfig;
import jep.python.PyObject;
import lombok.Getter;
import lombok.extern.slf4j.Slf4j;

/**
 * Raw Simulink model. We use the fixed step execution of Simulink to make sampling easier.
 */
@Slf4j
public class PythonModel {
    private final SharedInterpreter interpreter;

    @Getter
    private final PyObject pysul;
    public PythonModel(String initScript) throws JepException {
        SharedInterpreter.setConfig(new JepConfig().redirectStdout(System.out).redirectStdErr(System.err));
        this.interpreter = new SharedInterpreter();

        this.interpreter.runScript(initScript);
        //this.interpreter.eval(String.format("import %s as s", moduleName));
        this.interpreter.eval("sul = SUL()");
        this.pysul = this.interpreter.getValue("sul", PyObject.class);
    }
}
