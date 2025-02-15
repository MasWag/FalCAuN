from typing import Mapping, Tuple
from enum import auto, Enum

#StrEnum is available since 3.11
class State(Enum):
    Q0 = "q0"
    Q1 = "q1"
    Q2 = "q2"
    Q3 = "q3"

class InputSignal(Enum):
    A = "a"
    B = "b"

class OutputSignal(Enum):
    P = "p"
    Q = "q"

class SUL:
    mealy : Mapping[Tuple[State, InputSignal], Tuple[State, OutputSignal]]
    state : State

    def __init__(self):
        self.state = State.Q0
        self.mealy = {
            (State.Q0, InputSignal.A) : (State.Q1, OutputSignal.P),
            (State.Q0, InputSignal.B) : (State.Q2, OutputSignal.Q),
            (State.Q1, InputSignal.A) : (State.Q0, OutputSignal.Q),
            (State.Q1, InputSignal.B) : (State.Q3, OutputSignal.P),
            (State.Q2, InputSignal.A) : (State.Q3, OutputSignal.P),
            (State.Q2, InputSignal.B) : (State.Q0, OutputSignal.P),
            (State.Q3, InputSignal.A) : (State.Q2, OutputSignal.Q),
            (State.Q3, InputSignal.B) : (State.Q1, OutputSignal.Q),
        }

    def step(self, inputSignal : str) -> str:
        in_ = InputSignal(inputSignal)
        (next, out) = self.mealy[(self.state, in_)]
        self.state = next
        return out.value
    
    def pre(self) -> None:
        self.state = State.Q0
    def post(self) -> None:
        return 0
    def close(self) -> None:
        return 0
