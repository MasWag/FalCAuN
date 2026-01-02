from __future__ import annotations

import datetime
import importlib
import os
import sys
import time
import types
from pathlib import Path
from typing import Any, Callable, List, Optional, Tuple

import numpy as np
from abstract_sul import AbstractSUL
from simglucose.actuator.pump import InsulinPump
from simglucose.patient.t1dpatient import T1DPatient
from simglucose.sensor.cgm import CGMSensor
from simglucose.controller.base import Action as ControllerAction
from simglucose.simulation.env import T1DSimEnv
from simglucose.simulation.scenario import Action as ScenarioAction, Scenario
from sbx import PPO


class ContinuousGlucoseScenario(Scenario):
    def __init__(self, start_time: datetime.datetime):
        super().__init__(start_time=start_time)

    def set_action(self, meal: float) -> None:
        self.meal = meal

    def get_action(self, t: datetime.datetime) -> ScenarioAction:
        return ScenarioAction(meal=self.meal)

    def reset(self) -> None:
        pass


class PPOController:
    def __init__(
        self,
        model_path: Optional[Path] = None,
        deterministic: bool = True,
        device: str = "auto",
        action_bounds: Optional[Tuple[float, float]] = None,
    ):
        if "__file__" in globals():
            base_dir = Path(__file__).resolve().parent
        else:  # Jep runs scripts without defining __file__
            base_dir = Path.cwd()
        default_path = base_dir / "simglucose_rl" / "ppo.zip"
        self.model_path = Path(model_path) if model_path else default_path
        if not self.model_path.exists():
            raise FileNotFoundError(f"PPO policy not found at '{self.model_path}'")

        self.deterministic = deterministic
        self.device = device
        self.action_bounds = action_bounds

        self.model = None
        self.is_recurrent = False
        self._hidden_state = None
        self._episode_start = None
        self._fallback_reason: Optional[str] = None
        self._fallback_basal = self._compute_fallback_basal()

        self._load_model()

    def _compute_fallback_basal(self) -> float:
        if self.action_bounds is None:
            return 0.0
        low, high = self.action_bounds
        if low is not None and high is not None:
            return float(np.clip(0.0, low, high))
        if high is not None:
            return float(min(0.0, high))
        if low is not None:
            return float(max(0.0, low))
        return 0.0

    def _make_action(self, basal: float) -> ControllerAction:
        low = high = None
        if self.action_bounds is not None:
            low, high = self.action_bounds
        if low is not None:
            basal = max(basal, low)
        if high is not None:
            basal = min(basal, high)
        return ControllerAction(basal=float(basal), bolus=0.0)

    @staticmethod
    def _extract_basal(raw_action) -> float:
        if isinstance(raw_action, ControllerAction):
            return float(raw_action.basal)
        if isinstance(raw_action, (tuple, list)):
            if not raw_action:
                return 0.0
            return float(raw_action[0])
        arr = np.asarray(raw_action, dtype=np.float32).reshape(-1)
        if arr.size == 0:
            return 0.0
        return float(arr[0])

    def _init_fallback(self, reason: BaseException) -> None:
        self.model = None
        self.is_recurrent = False
        self._hidden_state = None
        self._episode_start = None
        self._fallback_reason = f"{type(reason).__name__}: {reason}"
        raise RuntimeError(
            "Fatal: failed to load the PPO policy; refusing to fall back to a "
            f"zero-action controller ({self._fallback_reason})."
        ) from reason

    def _load_model(self) -> None:
        self.model = PPO.load(self.model_path, device=self.device)
        self.is_recurrent = False

        self.reset()

    def reset(self) -> None:
        self._hidden_state = None
        if self.is_recurrent:
            self._episode_start = np.array([True], dtype=bool)
        else:
            self._episode_start = None

    def policy(self, obs, reward, done, **info):
        if self.model is None:
            if self._fallback_reason is not None:
                raise RuntimeError(
                    "PPO policy is unavailable because initialisation failed "
                    f"({self._fallback_reason})."
                )
            raise RuntimeError("PPO policy is unavailable; controller not initialised.")

        if self.is_recurrent:
            if done:
                self._hidden_state = None
                self._episode_start[0] = True
            else:
                self._episode_start[0] = False

            action, self._hidden_state = self.model.predict(
                obs,
                state=self._hidden_state,
                episode_start=self._episode_start,
                deterministic=self.deterministic,
            )
        else:
            action, _ = self.model.predict(obs, deterministic=self.deterministic)

        basal = self._extract_basal(action)
        return self._make_action(basal)


class SULBase(AbstractSUL):
    INF = 1e9

    def __init__(self, start_time: datetime.datetime, step_n: int, result_path: str):
        self.inputSignals: List[float] = []
        self.step_n = step_n
        self.result_path = result_path

        patient = T1DPatient.withName("adolescent#001")
        sensor = CGMSensor.withName("Dexcom", seed=1)
        pump = InsulinPump.withName("Insulet")

        scenario = ContinuousGlucoseScenario(start_time=start_time)
        self.scenario = scenario
        self.env = T1DSimEnv(patient, sensor, pump, scenario)

        min_basal = float(pump._params.get("min_basal", 0.0))
        max_basal = float(pump._params.get("max_basal", 0.0))
        self.controller = PPOController(action_bounds=(min_basal, max_basal))

        self.pre_bg = SULBase.INF

    def mini_step(self) -> Tuple[float, float]:
        obs, reward, done, info = self.state
        action = self.controller.policy(obs, reward, done, **info)
        self.state = self.env.step(action)

        row = self.results().iloc[-2]
        return row["BG"], row["insulin"]

    def step(self, inputSignal: List[float]) -> List[float]:
        assert len(inputSignal) == 1
        glucose = inputSignal[0]
        self.scenario.set_action(glucose)

        last_bg = 0.0
        sum_insulin = 0.0
        pre_bg = self.pre_bg
        max_bg = 0.0
        max_delta_bg = -SULBase.INF
        min_bg = SULBase.INF
        min_delta_bg = SULBase.INF

        for _ in range(self.step_n):
            bg, insulin = self.mini_step()

            last_bg = bg
            sum_insulin += insulin
            max_bg = max(max_bg, bg)
            min_bg = min(min_bg, bg)

            delta_bg = 0.0 if pre_bg == SULBase.INF else (bg - pre_bg) / self.env.sample_time
            pre_bg = bg
            max_delta_bg = max(max_delta_bg, delta_bg)
            min_delta_bg = min(min_delta_bg, delta_bg)

            self.scenario.set_action(0)

        self.pre_bg = last_bg

        return [last_bg, sum_insulin, min_bg, max_bg, min_delta_bg, max_delta_bg]

    def pre(self) -> None:
        self.controller.reset()
        self.state = self.env.reset()
        self.tic = time.time()
        self.pre_bg = SULBase.INF

    def post(self) -> None:
        toc = time.time()
        print(f"Simulation took {toc - self.tic} seconds.")
        self.save_results()

    def close(self) -> None:
        pass

    def results(self):
        return self.env.show_history()

    def save_results(self) -> None:
        df = self.results()
        if not os.path.isdir(self.result_path):
            os.makedirs(self.result_path, exist_ok=True)
        filename = os.path.join(self.result_path, f"{self.env.patient.name}.csv")
        df.to_csv(filename)
        print(f"Saved output to {filename}")


class SUL(SULBase):
    def __init__(self):
        now = datetime.datetime.now()
        start_time = datetime.datetime.combine(now.date(), datetime.datetime.min.time())
        step_n = 10
        super().__init__(start_time, step_n, "./results")
