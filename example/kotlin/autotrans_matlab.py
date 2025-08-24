import sys
sys.path.append(".")

import os
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
    isInitial : bool
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
        self.eng = matlab.engine.start_matlab() if len(engines) == 0 else matlab.engine.connect_matlab()

        self.eng.clear(nargout=0)
        self.eng.warning('off', 'Simulink:LoadSave:EncodingMismatch')
        self.eng.workspace["signalStep"] = signalStep

        initScript(self.eng)

        self.reset()

    def step(self, inputSignal : List[float]) -> Tuple[List[float], List[List[float]]]:
        assert self.isInitial or not inputSignal
        self.inputSignal.add(inputSignal)
        return self.exec_aux()

    def exec(self, inputSignals: List[List[float]]) -> Tuple[List[float], List[List[float]]]:
        assert self.isInitial or not inputSignals

        for e in inputSignals:
            self.inputSignal.add(e)

        return self.exec_aux()

    def exec_aux(self):
        # For efficiency, we use StringBuilder to make the entire script to execute in MATLAB rather than evaluate each line.

        # Make the input signal
        self.make_dataset()
        self.configureSimulink()
        self.preventHugeTempFile()

        # Execute the simulation
        self.eng.set_param(self.mdl,'SaveFinalState','on','FinalStateName', 'myOperPoint','SaveCompleteFinalSimState','on', nargout=0)
        if self.isInitial:
            self.eng.set_param(self.mdl, 'LoadInitialState', 'off', nargout=0)
            self.isInitial = False
        else:
            self.eng.set_param(self.mdl, 'LoadInitialState', 'on', nargout=0)
            self.eng.set_param(self.mdl, 'InitialState', 'myOperPoint', nargout=0)
        

        # Run the simulation
        self.runSimulation(self.inputSignal.duration())

        # get the simulation result and make the result
        y = self.getResult()
        t = self.getTimestamps()
        assert(len(t) == len(y))

        # Final internal process
        assert not self.isInitial

        return (t, y)

    def reset(self) -> None:
        self.inputSignal = Signal(self.signalStep)
        self.isInitial = True
        self.counter += 1

    def close(self) -> None:
        self.eng.close()
    
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
        eng = self.eng
        ySize = eng.size(eng.workspace["y"])[0]
        
        if self.inputSignal.duration() == 0.0:
            tmpY = []
            if ySize[1] == 1.0 :
                # When the output is one dimensional, we need to convert it to 1D array first.
                tmp : float = eng.workspace["y"]
                tmpY = [tmp]
            else:
                tmpY = eng.workspace["y"]

            if tmpY == []:
                # The simulation output is null
                y = []
            else:
                y = [tmpY]

        else:
            if ySize[1] == 1.0:
                # When the output is one dimensional, we need to convert it to 2D array.
                tmpY = eng.workspace["y"]
                y = [[d] for d in tmpY]
            else:
                y = eng.workspace["y"]
        
        return y

    def getTimestamps(self) -> List[float]:
        if self.inputSignal.duration() == 0.0 :
            return [0.0]
        else:
            return self.eng.workspace["t"]

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

        versionString = eng.version('-release')
        oldpath = eng.path()
        userpath = eng.userpath()
        arg0 = os.path.join(userpath, "Examples", versionString, "simulink_automotive", "ModelingAnAutomaticTransmissionControllerExample")
        eng.path(arg0, oldpath)

        eng.load_system(SUL.MDL, nargout=0)

    def __init__(self):
        paramNames = ["throttle", "brake"]
        signalStep = 1.0
        simulinkSimulationStep = 0.0025
        self.simulinkModel = SimulinkModel(SUL.initScript, SUL.MDL, paramNames, signalStep, simulinkSimulationStep)

    def step(self, inputSignal : List[float]) -> List[List[float]]:
        """
        Returns an array 'ary' : ary[i][0] is the time, and ary[i][1:] is the output signal.
        """

        (t, y) = self.simulinkModel.step(inputSignal)
        y = np.array(y[0], dtype=np.float64)
        t = np.array(t, dtype=np.float64)

        ary = []
        for i in range(len(y)):
            a = np.insert(y[i], 0, t[i])
            ary.append(list(a))

        ret = np.array(ary, dtype=np.float64)
        return ret.tolist()

    def exec(self, inputSignals: List[List[float]]) -> List[List[float]]:
        (t, y) = self.simulinkModel.exec(inputSignals)
        y = np.array(y[0], dtype=np.float64)
        t = np.array(t, dtype=np.float64)

        # Convert the result to numpy array
        ary = []
        for i in range(len(y)):
            a = np.insert(y[i], 0, t[i])
            ary.append(list(a))

        ret = np.array(ary, dtype=np.float64)
        return ret.tolist()
    
    def pre(self) -> None:
        self.simulinkModel.reset()

    def post(self) -> None:
        self.simulinkModel.reset()

    def close(self) -> None:
        self.simulinkModel.close()
