import sys
sys.path.append(".")

import os
import shutil
import tempfile
from abstract_sul import AbstractSUL
from typing import List, Callable, Tuple
import matlab.engine
import matlab
import numpy as np

class Signal:
    """
    Equivalent to Signal
    """

    timestamps : List[float]
    signalValue : List[List[float]]
    timeStep : float
    def __init__(self, timeStep):
        self.timeStep = timeStep
        self.timestamps = []
        self.signalValue = []

    def getTimestamps(self) -> List[float]:
        return self.timestamps

    def duration(self) -> float:
        return 0.0 if len(self.timestamps) == 0 else self.timestamps[-1]
    
    def add(self, inputValue : List[float]) -> None:
        if len(self.timestamps) == 0:
            self.timestamps.append(0.0)
        else:
            self.timestamps.append(self.duration() + self.timeStep)
        self.signalValue.append(inputValue)

    def dimension(self) -> int:
        if len(self.signalValue) == 0:
            return 0
        else:
            return len(self.signalValue[0])
    
    def dimensionGet(self, index) -> List[float]:
        return [s[index] for s in self.signalValue]



class SimulinkModel:
    """
    Compatible implementation of SimulinkModel
    """

    mdl : str
    paramNames : List[str]
    signalStep : float
    simulinkSimulationStep : float
    inputSignal : Signal

    eng : matlab.engine.MatlabEngine
    counter : int
    useFastRestart = True
    def __init__(
        self,
        initScript: Callable[[matlab.engine.MatlabEngine], None],
        mdl: str,
        paramNames: List[str],
        signalStep: float,
        simulinkSimulationStep: float
    ) -> None:
        self.mdl = mdl
        self.paramNames = paramNames
        self.signalStep = signalStep
        self.simulinkSimulationStep = simulinkSimulationStep
        self.counter = 0

        engines = matlab.engine.find_matlab()
        # Connect to a shared MATLAB session if any (e.g., in the Docker image). Otherwise, start a new one.
        self.ownsEngine = len(engines) == 0
        self.eng = matlab.engine.start_matlab() if self.ownsEngine else matlab.engine.connect_matlab()

        self.eng.clear(nargout=0)
        self.eng.warning('off', 'Simulink:LoadSave:EncodingMismatch')
        # Use dedicated Simulink cache and code generation folders, as FalCAuN's SimulinkModel does, so that
        # build artifacts of another MATLAB release in the current directory (e.g., slprj) are never reused.
        self.fileGenDir = tempfile.mkdtemp(prefix="falcaun-sl-py-")
        self.eng.workspace["falcaunFileGenDir"] = self.fileGenDir
        self.eng.eval("Simulink.fileGenControl('set', 'CacheFolder', falcaunFileGenDir, 'CodeGenFolder', falcaunFileGenDir);"
                      " clear falcaunFileGenDir;", nargout=0)
        self.eng.workspace["signalStep"] = signalStep

        initScript(self.eng)

        # Simulate in the private folder, as FalCAuN's SimulinkModel does, so that simulation artifacts in the
        # original current directory (e.g., *.slxc or slprj of another release) never shadow the new ones.
        self.previousDir = self.eng.cd(self.fileGenDir)

        self.reset()

    def step(self, inputSignal : List[float]) -> Tuple[List[float], List[List[float]]]:
        """
        Appends inputSignal and simulates the whole input signal so far from the initial state.

        As FalCAuN's SimulinkModel does, the accumulated input is replayed from the initial state instead of loading
        the final state of the previous simulation. The result is the whole trace from time 0.
        """
        self.inputSignal.add(inputSignal)
        return self.exec_aux()

    def exec(self, inputSignals: List[List[float]]) -> Tuple[List[float], List[List[float]]]:
        """
        Appends inputSignals and simulates the whole input signal so far from the initial state.
        """
        for e in inputSignals:
            self.inputSignal.add(e)

        return self.exec_aux()

    def exec_aux(self) -> Tuple[List[float], List[List[float]]]:
        # Make the input signal
        self.make_dataset()
        self.configureSimulink()
        self.preventHugeTempFile()

        # Always simulate from the initial state
        self.eng.set_param(self.mdl, 'SaveFinalState', 'off', nargout=0)
        self.eng.set_param(self.mdl, 'LoadInitialState', 'off', nargout=0)

        # Run the simulation
        self.runSimulation(self.inputSignal.duration())
        self.counter += 1

        # get the simulation result
        t = self.getTimestamps()
        y = self.getResult()
        if len(t) != len(y):
            raise RuntimeError(f"Inconsistent simulation result: {len(t)} timestamps and {len(y)} output samples")

        return (t, y)

    def reset(self) -> None:
        self.inputSignal = Signal(self.signalStep)

    def close(self) -> None:
        if self.ownsEngine:
            # Terminate the MATLAB session started by this object
            self.eng.quit()
        else:
            # Keep the shared MATLAB session running, and restore its folders
            self.eng.cd(self.previousDir, nargout=0)
            self.eng.eval("Simulink.fileGenControl('reset');", nargout=0)
        shutil.rmtree(self.fileGenDir, ignore_errors=True)
    
    def make_dataset(self) -> None:
        eng = self.eng
        timeVector = matlab.double(self.inputSignal.getTimestamps())
        ds = eng.Simulink.SimulationData.Dataset()
        for i in range(0, self.inputSignal.dimension()):
            tmp = matlab.double(self.inputSignal.dimensionGet(i))
            input = eng.timeseries(tmp, timeVector)

            #eng.setfield(eng.getfield(input, "DataInfo"), "Interpolation", eng.tsdata.interpolation('zoh'))
            
            # Assume InterpolationMethod is LINEAR
            eng.setfield(eng.getfield(input, "DataInfo"), "Interpolation", eng.tsdata.interpolation('linear'))
            
            ds = eng.addElement(ds, input, self.paramNames[i])
        eng.workspace["ds"] = ds

    def configureSimulink(self) -> None:
        eng = self.eng
        mdl = self.mdl
        # We use the data in ds
        eng.set_param(mdl, 'LoadExternalInput', 'on', nargout=0)
        eng.set_param(mdl, 'ExternalInput', 'ds', nargout=0)

        # Enable fast restart
        if self.useFastRestart:
            # Switch FastRestart on
            eng.set_param(mdl,'FastRestart','on', nargout=0)
        else:
            eng.set_param(mdl,'FastRestart','off', nargout=0)

        ## Configuration on the accelerator
        # Use normal mode
        # eng.set_param(mdl,'SimulationMode','normal', nargout=0)
        # Enable accelerator mode
        eng.set_param(mdl,'SimulationMode','accelerator', nargout=0)
        # Enable classic accelerator mode
        eng.set_param(0, 'GlobalUseClassicAccelMode', 'on', nargout=0)


        # The save format must be an array
        eng.set_param(mdl, 'SaveFormat', 'Array', nargout=0)
        # We save the output as yout
        eng.set_param(mdl, 'SaveOutput', 'on', nargout=0)
        eng.set_param(mdl, 'OutputSaveName', 'yout', nargout=0)
        # We save the time as tout
        eng.set_param(mdl, 'SaveTime', 'on', nargout=0)
        eng.set_param(mdl, 'TimeSaveName', 'tout', nargout=0)

        # Configuration on the decimation
        eng.set_param(mdl, 'SolverType', 'Fixed-step', nargout=0)
        eng.set_param(mdl, 'FixedStep', str(self.simulinkSimulationStep), nargout=0)
        # We dump all the results
        eng.set_param(mdl, 'LimitDataPoints', 'off', nargout=0)
        # We do not decimate the result
        # eng.set_param(mdl, 'Decimation', signalStep / simulinkSimulationStep, nargout=0)

    
    def preventHugeTempFile(self) -> None:
        eng = self.eng
        eng.Simulink.sdi.setAutoArchiveMode(False, nargout=0)
        eng.Simulink.sdi.setArchiveRunLimit(0, nargout=0)
        eng.Simulink.sdi.clear(nargout=0)

    def runSimulation(self, stopTime : float) -> None:
        eng = self.eng

        # append the input signal
        eng.workspace["in"] = eng.Simulink.SimulationInput(self.mdl)
        eng.workspace["in"] = eng.eval("in.setExternalInput(ds)")

        # Set the StopTime
        eng.workspace["in"] = eng.eval("in.setModelParameter('StopTime', '{}')".format(stopTime))
        # Save the output to yout
        if not self.useFastRestart:
            eng.workspace["in"] = eng.eval("in.setModelParameter('SaveOutput', 'on')")
            eng.workspace["in"] = eng.eval("in.setModelParameter('OutputSaveName', 'yout')")
            eng.workspace["in"] = eng.eval("in.setModelParameter('SaveTime', 'on')")
            eng.workspace["in"] = eng.eval("in.setModelParameter('TimeSaveName', 'tout')")

        eng.workspace["in"] = eng.eval("in.setModelParameter('LoadInitialState', 'off')")

        # Execute the simulation
        eng.workspace["simOut"] = eng.sim(eng.workspace["in"])
        
        # We handle the output as double.
        eng.workspace["y"] = eng.eval("double(simOut.get('yout'))")
        eng.workspace["t"] = eng.eval("double(simOut.get('tout'))")
    
    
    def getResult(self) -> List[List[float]]:
        """
        Returns the output signal of the last simulation: one row of the output values for each timestamp.
        """
        y = np.asarray(self.eng.workspace["y"], dtype=np.float64)
        # A simulation with one output (or one timestamp) may return a vector or a scalar
        return y.reshape(len(self.getTimestamps()), -1).tolist()

    def getTimestamps(self) -> List[float]:
        """
        Returns the timestamps of the last simulation.
        """
        return np.asarray(self.eng.workspace["t"], dtype=np.float64).reshape(-1).tolist()

def benchmark_init_script(relative_path: str) -> str:
    """
    Returns the absolute path of the shared FalCAuN benchmark definition benchmarks/simulink/<relative_path>.

    The root of the FalCAuN repository is searched upwards from the directory of this file or, when this file is
    executed by Jep, which does not define __file__, from the current working directory.
    """
    start = os.path.dirname(os.path.realpath(__file__)) if "__file__" in globals() else os.getcwd()
    directory = os.path.abspath(start)
    while True:
        candidate = os.path.join(directory, "benchmarks", "simulink", relative_path)
        if os.path.isfile(candidate):
            return os.path.realpath(candidate)
        parent = os.path.dirname(directory)
        if parent == directory:
            raise FileNotFoundError(f"benchmarks/simulink/{relative_path} is not found. "
                                    "Run this example inside the FalCAuN repository.")
        directory = parent

class SUL(AbstractSUL):
    """
    Python wrapped SUL using the Autotrans_shift Simulink model
    """

    simulinkModel : SimulinkModel
    MDL = "Autotrans_shift"

    def initScript(eng : matlab.engine.MatlabEngine) -> None:
        """
        Compatible to `initScript` in AutoTrans.kt
        """

        # Run the shared FalCAuN benchmark definition by its absolute path.
        # See benchmarks/simulink/AT/initAT.m for the details, e.g., the model and the unit conversion.
        eng.run(benchmark_init_script(os.path.join("AT", "initAT.m")), nargout=0)

    def __init__(self):
        paramNames = ["throttle", "brake"]
        signalStep = 1.0
        simulinkSimulationStep = 0.0025
        self.simulinkModel = SimulinkModel(SUL.initScript, SUL.MDL, paramNames, signalStep, simulinkSimulationStep)

    @staticmethod
    def to_rows(t: List[float], y: List[List[float]]) -> List[List[float]]:
        """
        Returns rows whose first column is the timestamp and whose remaining columns are the output values.
        """
        return [[ti] + yi for ti, yi in zip(t, y)]

    def step(self, inputSignal : List[float]) -> List[List[float]]:
        """
        Returns the whole trace from time 0: ary[i][0] is the time, and ary[i][1:] is the output signal.
        """
        (t, y) = self.simulinkModel.step(inputSignal)
        return SUL.to_rows(t, y)

    def exec(self, inputSignals: List[List[float]]) -> List[List[float]]:
        """
        Returns the whole trace from time 0: ary[i][0] is the time, and ary[i][1:] is the output signal.
        """
        (t, y) = self.simulinkModel.exec(inputSignals)
        return SUL.to_rows(t, y)

    def pre(self) -> None:
        self.simulinkModel.reset()

    def post(self) -> None:
        self.simulinkModel.reset()

    def close(self) -> None:
        self.simulinkModel.close()
