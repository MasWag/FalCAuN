import sys
sys.path.append(".")

from abstract_sul import AbstractSUL
from typing import List
import datetime
import os
import time

from simglucose.simulation.env import T1DSimEnv
from simglucose.simulation.scenario import Scenario, Action
from simglucose.controller.basal_bolus_ctrller import BBController, Controller
from simglucose.sensor.cgm import CGMSensor
from simglucose.actuator.pump import InsulinPump
from simglucose.patient.t1dpatient import T1DPatient


# A scenario that implements set_action, a method to change the meal input dynamically.
class ContinuousGlucoseScenario(Scenario):
    def __init__(self, start_time):
        Scenario.__init__(self, start_time=start_time)
    
    def set_action(self, meal):
        self.meal = meal

    def get_action(self, t):
        return Action(meal=self.meal)

    def reset(self):
        pass

# A class for SUL based on SimObj
class SULBase(AbstractSUL):
    controller : Controller
    result_path : str
    INF = 1e9

    def __init__(self, start_time, step_n, result_path):
        self.inputSignals = []
        self.step_n = step_n
        self.result_path = result_path

        # Create a simulation environment
        patient = T1DPatient.withName('adolescent#001')
        sensor = CGMSensor.withName('Dexcom', seed=1)
        pump = InsulinPump.withName('Insulet')

        # Create a controller
        self.controller = BBController()

        scenario = ContinuousGlucoseScenario(start_time=start_time)
        self.scenario = scenario
        self.env = T1DSimEnv(patient, sensor, pump, scenario)

        self.pre_bg = SULBase.INF

    def mini_step(self):
        obs, reward, done, info = self.state
        action = self.controller.policy(obs, reward, done, **info)
        self.state = self.env.step(action)

        # The last row does not contain some data ("CHO" and "insulin" are not set) so we use the second last row
        row = self.results().iloc[-2]
        #return [row["BG"], row["CGM"], row["CHO"], row["insulin"], row["LBGI"], row["HBGI"], row["Risk"]]
        return (row["BG"], row["insulin"])

    # inputSignal : [glucose]
    def step(self, inputSignal : List[float]) -> List[float]:
        assert len(inputSignal) == 1
        glucose = inputSignal[0]

        # Set glucose for each step
        self.scenario.set_action(glucose)

        (last_bg, sum_insulin) = (0.0, 0.0)
        pre_bg = self.pre_bg
        max_bg = 0.0
        max_delta_bg = -SULBase.INF
        (min_bg, min_delta_bg) = (SULBase.INF, SULBase.INF)
        for i in range(self.step_n):
            (bg, insulin) = self.mini_step()

            # Calculate statistics, used as the return values
            last_bg = bg
            sum_insulin += insulin
            max_bg = max(max_bg, bg)
            min_bg = min(min_bg, bg)
            delta_bg = 0.0 if pre_bg == SULBase.INF else (bg - pre_bg) / self.env.sample_time
            pre_bg = bg
            max_delta_bg = max(max_delta_bg, delta_bg)
            min_delta_bg = min(min_delta_bg, delta_bg)
            self.scenario.set_action(0) # Reset CHO to 0 after first iteration

        self.pre_bg = last_bg
        # print(last_bg, sum_insulin, min_bg, max_bg, min_delta_bg, max_delta_bg)
        return [last_bg, sum_insulin, min_bg, max_bg, min_delta_bg, max_delta_bg]

    def pre(self) -> None:
        # Put them together to create a simulation object
        print("Process ID: {}".format(os.getpid()))

        self.controller.reset()
        self.state = self.env.reset()
        self.tic = time.time()
        self.pre_bg = SULBase.INF

    def post(self) -> None:
        toc = time.time()
        print('Simulation took {} seconds.'.format(toc - self.tic))
        self.save_results()

    def close(self) -> None:
        pass


    def results(self):
        return self.env.show_history()

    def save_results(self):
        df = self.results()
        if not os.path.isdir(self.result_path):
            os.makedirs(self.result_path, exist_ok=True)
        filename = os.path.join(self.result_path, str(self.env.patient.name) + '.csv')
        df.to_csv(filename)
        print("Saved output to {}".format(filename))


class SUL(SULBase):
    def __init__(self):
        # specify start_time as the beginning of today
        now = datetime.datetime.now()
        start_time = datetime.datetime.combine(now.date(), datetime.datetime.min.time())
        step_n = 10 # The number of mini_step iterations. Elapse CGMSensor.sample_time * step_n
        super().__init__(start_time, step_n, "./results")


# Below part is executed even if PythonModel calls this file
#if __name__ == "__main__":
#    sul = SUL()
#    sul.pre()
#    for i in range(0, 60*24//3):
#        sul.step([numpy.random.exponential(1)])
#    sul.post()
