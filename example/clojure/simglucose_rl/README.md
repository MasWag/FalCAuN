# SimGlucose PPO Controller

This directory bundles a pre-trained PPO controller (`ppo.zip`) together with
supporting scripts that can be used with the SimGlucose environment.

## Quick Start

1. Install the requirements:
   ```bash
   pip install -r requirements.txt
   ```
2. Drive the simulator with the PPO policy via the `SUL` wrapper:
   ```python
   from simglucose_rl import SUL
   sul = SUL()
   sul.pre()
   observation = sul.step([0.0])  # replace with your meal input
   sul.post()
   ```

The wrapper mirrors the `simglucose_bb.SUL` interface so it can be swapped into
existing experiments without further changes.

## Visualising the Policy

Use `enjoy.py` to render a rollout:
```bash
python enjoy.py --model_path ppo.zip --model_kind PPO
```

Pass `RecurrentPPO` to `--model_kind` if you switch to a recurrent checkpoint.

## Files

- `ppo.zip`: Pre-trained PPO weights.
- `enjoy.py`: Minimal script to load a model and interactively render the simulator.
