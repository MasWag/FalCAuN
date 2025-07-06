from typing import List

EPS = 1e-6
class SUL:
    static_friction = 0.25  # static friction coefficient
    dynamic_friction = 0.125  # dynamic friction coefficient
    dt = 0.125     # time step
    def __init__(self):
        self.time = 0.0  # current time
        self.velocity = 0.0
        self.outputs = []

    def ministep(self, acc) -> List[float]:
        self.time += SUL.dt
        if abs(self.velocity) < EPS:
            acc -= SUL.static_friction
        else:
            acc -= SUL.dynamic_friction

        self.velocity = max(0.0, self.velocity + acc * self.dt)
        return [self.time, self.velocity]

    def step(self, inputSignal: List[float]) -> List[List[float]]:
        [acc] = inputSignal
        if self.outputs == []:
            self.outputs = [[0.0, 0.0]]
            return self.outputs

        for _e in range(8):
            self.outputs.append(self.ministep(acc))

        return self.outputs

    def exec(self, inputSignals: List[List[float]]) -> List[List[float]]:
        for e in inputSignals:
            self.step(e)
        return self.outputs

    def pre(self):
        self.time = 0.0
        self.velocity = 0.0
        self.outputs = []

    def post(self):
        pass
    def close(self):
        pass
