from typing import List
import datetime

from simglucose.simulation.env import T1DSimEnv
from simglucose.simulation.user_interface import simulate
from simglucose.simulation.scenario import CustomScenario
from simglucose.simulation.sim_engine import SimObj, sim, batch_sim
from simglucose.controller.basal_bolus_ctrller import BBController, Controller
from simglucose.sensor.cgm import CGMSensor
from simglucose.actuator.pump import InsulinPump
from simglucose.patient.t1dpatient import T1DPatient


class SULBase:
    fixed_env : any
    controller : Controller
    time_list : List[int]
    start_time : datetime.datetime
    timedelta : datetime.timedelta
    len_time_list : int
    result_path : str
    inputSignals : List[int]

    def __init__(self, time_list, start_time, timedelta, result_path):
        self.inputSignals = []
        self.time_list = time_list
        self.len_time_list = len(self.time_list)
        self.start_time = start_time
        self.timedelta = timedelta
        self.result_path = result_path

        # Create a simulation environment
        patient = T1DPatient.withName('adolescent#001')
        sensor = CGMSensor.withName('Dexcom', seed=1)
        pump = InsulinPump.withName('Insulet')
        self.fixed_env = (patient, sensor, pump)

        # Create a controller
        self.controller = BBController()

    def step(self, inputSignal : List[float]) -> List[float]:
        assert len(inputSignal) == 1
        self.inputSignals.append(inputSignal[0])

        (patient, sensor, pump) = self.fixed_env

        hour = self.time_list[(len(self.inputSignals)-1) % self.len_time_list]
        #scen = list(zip(self.time_list, self.inputSignals))
        scen=[]
        for i, e in enumerate(self.inputSignals):
            scen.append((self.time_list[i % self.len_time_list], e))
        print(scen)
        scenario = CustomScenario(start_time=self.start_time, scenario=scen)
        env = T1DSimEnv(patient, sensor, pump, scenario)

        # Put them together to create a simulation object
        so = SimObj(env, self.controller, self.timedelta, animate=False, path=self.result_path)
        results = sim(so) #: pandas.DataFrame
        time = self.start_time + datetime.timedelta(hours=hour)
        row = results.loc[time]
        #ret = [row["BG"], row["CGM"], row["CHO"], row["insulin"], row["LBGI"], row["HBGI"], row["Risk"]]
        ret = [row["BG"], row["insulin"]]
        return ret
    
    def pre(self) -> None:
        return 0
    def post(self) -> None:
        return 0
    def close(self) -> None:
        return 0

class SUL(SULBase):
    def __init__(self):
        # specify start_time as the beginning of today
        now = datetime.datetime.now()
        start_time = datetime.datetime.combine(now.date(), datetime.datetime.min.time())
        delta = datetime.timedelta(days=1)
        super().__init__([7, 12, 16, 18, 23], start_time, delta, "./result")


if __name__ == "__main__":
    #BG が範囲内にあるか？を仕様で書く
    sul = SUL()
    sul.pre()
    sul.step([40]) #7時
    sul.step([40]) #12時
    sul.step([40]) #16時
    sul.step([40]) #18時
    sul.step([40]) #23時
    sul.post()
