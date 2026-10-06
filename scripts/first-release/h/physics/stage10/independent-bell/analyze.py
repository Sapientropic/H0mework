"""Apply the pre-selection Bell family to a metadata-defined trial stream."""

from __future__ import annotations

import importlib.util
from itertools import islice
from pathlib import Path

from predict import tables


BASE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location(
    "frozen_bell_statistics", BASE.parent / "delft-bell/statistics.py")
stats = importlib.util.module_from_spec(spec)
spec.loader.exec_module(stats)
TRIAL_CAP = 100_000


def analyze(trials, instrument):
    """Score the first fixed-cap accepted trials without inspecting later outcomes.

    The archive-specific parser determines eligibility from the documented
    protocol. It preserves acquisition order and supplies h/a/b/x/y plus any
    provenance. Source selection and information-isolation claims live in the
    custody record, not in this numerical function.
    """
    prediction = tables(instrument)
    models = prediction["models"]
    processes = []
    for model in models:
        point = {(r["herald"], r["a"], r["b"]): r["probabilities"]
                 for r in model["table"]}
        processes.append(stats.BellEProcess(predictions=point, radii=stats.RADIUS_GRID))
    first = last = None
    for trial in islice(trials, TRIAL_CAP):
        for process in processes:
            process.update(trial)
        identity = {k: trial[k] for k in ("source_file", "source_line") if k in trial}
        if first is None:
            first = identity
        last = identity
    if not processes[0].n_trials:
        raise ValueError("no eligible trials; an empty stream is not a model verdict")
    results = []
    for model, process in zip(models, processes):
        result = process.result()
        for radius in result["radii"]:
            radius["reject_at_model_alpha"] = radius["anytime_p"] <= model["alpha"]
        results.append({"id": model["id"], "alpha": model["alpha"], **result})
    return {"schema": "source-fixed-independent-bell-analysis/v1",
            "trial_cap": TRIAL_CAP, "first_trial": first, "last_trial": last,
            "family_alpha_max": prediction["family_alpha_max"],
            "radius_role": "predeclared conditional sensitivity; no fitted error radius",
            "predictions": prediction, "models": results}
