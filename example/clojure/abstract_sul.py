from abc import ABC, abstractmethod

class AbstractSUL(ABC):
    """
    Abstract class for a SUL in Python.
    """

    def __init__(self):
        pass

    @abstractmethod
    def step(self, inputSignal):
        pass

    @abstractmethod
    def pre(self) -> None:
        pass

    @abstractmethod
    def post(self) -> None:
        pass

    @abstractmethod
    def close(self) -> None:
        pass

