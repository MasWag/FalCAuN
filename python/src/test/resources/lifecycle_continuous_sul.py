from typing import List

# Records the lifecycle events to this file so that the Java tests can check them.
EVENT_LOG = "./target/python_lifecycle_events.txt"


def record(event: str):
    with open(EVENT_LOG, "a") as f:
        f.write(event + "\n")


class SUL:
    """
    The output at time i is the running sum of the first input. The step fails if the input is negative.
    The signal step must be 1.0.
    """
    def __init__(self):
        self.outputs = []

    def pre(self):
        record("pre")
        self.outputs = []

    def step(self, inputSignal: List[float]) -> List[List[float]]:
        record("step")
        if inputSignal[0] < 0:
            raise ValueError("negative input")
        if self.outputs:
            [time, value] = self.outputs[-1]
            self.outputs.append([time + 1.0, value + inputSignal[0]])
        else:
            self.outputs.append([0.0, inputSignal[0]])
        return self.outputs

    def post(self):
        record("post")

    def close(self):
        record("close")
