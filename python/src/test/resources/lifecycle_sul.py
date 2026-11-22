from typing import List

# Records the lifecycle events to this file so that the Java tests can check them.
EVENT_LOG = "./target/python_lifecycle_events.txt"


def record(event: str):
    with open(EVENT_LOG, "a") as f:
        f.write(event + "\n")


class SUL:
    """
    Returns the running sum of the first input. The step fails if the input is negative.
    """
    def __init__(self):
        self.sum = 0.0

    def pre(self):
        record("pre")
        self.sum = 0.0

    def step(self, inputSignal: List[float]) -> List[float]:
        record("step")
        if inputSignal[0] < 0:
            raise ValueError("negative input")
        self.sum += inputSignal[0]
        return [self.sum]

    def post(self):
        record("post")

    def close(self):
        record("close")
