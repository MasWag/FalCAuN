from typing import List
import datetime
import os
import time
import numpy.random

from simglucose.simulation.env import T1DSimEnv
from simglucose.simulation.user_interface import simulate
from simglucose.simulation.scenario import Scenario, CustomScenario, Action
from simglucose.simulation.sim_engine import SimObj, sim, batch_sim
from simglucose.controller.basal_bolus_ctrller import BBController, Controller
from simglucose.sensor.cgm import CGMSensor
from simglucose.actuator.pump import InsulinPump
from simglucose.patient.t1dpatient import T1DPatient


class ContinuousGlucoseScenario(Scenario):
    def __init__(self, start_time):
        Scenario.__init__(self, start_time=start_time)
    
    def set_action(self, meal):
        self.meal = meal

    def get_action(self, t):
        return Action(meal=self.meal)

    def reset(self):
        pass

# Unfold SimObj
class SULBase:
    fixed_env : any
    controller : Controller
    start_time : datetime.datetime
    timedelta : datetime.timedelta
    len_time_list : int
    result_path : str
    inputSignals : List[int]

    def __init__(self, start_time, step_n, result_path):
        self.inputSignals = []
        self.start_time = start_time
        self.step_n = step_n
        self.result_path = result_path

        # Create a simulation environment
        patient = T1DPatient.withName('adolescent#001')
        sensor = CGMSensor.withName('Dexcom', seed=1)
        pump = InsulinPump.withName('Insulet')

        # Create a controller
        self.controller = BBController()

        scenario = ContinuousGlucoseScenario(start_time=self.start_time)
        self.scenario = scenario
        self.env = T1DSimEnv(patient, sensor, pump, scenario)

    def mini_step(self):
        obs, reward, done, info = self.state
        #if self.animate:
        #    self.env.render()
        action = self.controller.policy(obs, reward, done, **info)
        self.state = self.env.step(action)

        row = self.results().iloc[-2]
        #ret = [row["BG"], row["CGM"], row["CHO"], row["insulin"], row["LBGI"], row["HBGI"], row["Risk"]]
        return (row["BG"], row["insulin"])

    # inputSignal : [glucose]
    def step(self, inputSignal : List[float]) -> List[float]:
        assert len(inputSignal) == 1
        glucose = inputSignal[0]

        # Set glucose for each step
        self.scenario.set_action(glucose)

        INF=1e9
        (last_bg, sum_insulin) = (0.0, 0.0)
        max_bg = 0.0
        min_bg = INF
        for i in range(self.step_n):
            (bg, insulin) = self.mini_step()
            last_bg = bg
            sum_insulin += insulin
            max_bg = max(max_bg, bg)
            min_bg = min(min_bg, bg)
            self.scenario.set_action(0) # Reset CHO to 0 after first iteration

        print(last_bg, sum_insulin, max_bg)
        return [last_bg, sum_insulin, max_bg]

    def pre(self) -> None:
        # Put them together to create a simulation object
        print("Process ID: {}".format(os.getpid()))

        self.controller.reset()
        self.state = self.env.reset()
        self.tic = time.time()


    def post(self) -> None:
        #self.so.simulate()
        toc = time.time()
        print('Simulation took {} seconds.'.format(toc - self.tic))
        self.save_results()
        #self.so.save_results()
        #return self.so.results()
        return 0
    
    def results(self):
        return self.env.show_history()

    def save_results(self):
        df = self.results()
        if not os.path.isdir(self.result_path):
            os.makedirs(self.result_path)
        filename = os.path.join(self.result_path, str(self.env.patient.name) + '.csv')
        df.to_csv(filename)
        print("Saved output to {}".format(filename))
    
    def close(self) -> None:
        return 0

class SUL(SULBase):
    def __init__(self):
        # specify start_time as the beginning of today
        now = datetime.datetime.now()
        start_time = datetime.datetime.combine(now.date(), datetime.datetime.min.time())
        step_n = 10 # The number of mini_step iterations. Elapse CGMSensor.sample_time * step_n
        super().__init__(start_time, step_n, "./results")


if __name__ == "__main__":
    #BG が範囲内にあるか？を仕様で書く
    sul = SUL()
    sul.pre()
    for i in range(0, 60*24//3):
        sul.step([numpy.random.exponential(1)])
    sul.post()
