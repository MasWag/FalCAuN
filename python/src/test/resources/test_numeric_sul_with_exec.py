from typing import List

class SUL:
    def __init__(self):
        self.state = (0.0, 0.0)

    def step(self, inputSignal: List[float]) -> List[float]:
        """
        The first output is truncated to 100.0 if it exceeds 100.0.
        The second output is the sum modulo 100.0.
        """

        [sum0, sum1] = self.state
        sum0 = sum0 + sum(inputSignal)
        sum0 = max(0.0, min(100.0, sum0))
        sum1 = (sum1 + sum(inputSignal)) % 100.0
        self.state = [sum0, sum1]
        return self.state
    
    def exec(self, inputSignals: List[List[float]]) -> List[List[float]]:
        ret = []
        for e in inputSignals:
            ret.append(self.step(e))
        return ret

    def pre(self):
        self.state = (0.0, 0.0)
        
    def post(self):
        pass
    def close(self):
        pass
