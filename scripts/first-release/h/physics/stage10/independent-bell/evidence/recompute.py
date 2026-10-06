#!/usr/bin/env python3
"""Independent capped parser and 80-digit replay; imports no production core.

E_d(t) = [sum_j prod_i r_ji / 7] / prod_i min(1, q_i+d).
The numerator mixture is shared across all radii; KT uses prior context counts.
Every prefix is evaluated. Exp terms below exp(-200) may be omitted: the
absolute log-mixture error is at most 6*exp(-200), below the 80-digit budget
at the retained magnitudes. No uncapped event or other ZIP member is parsed.
"""

from datetime import datetime, timezone
from decimal import Decimal as D, localcontext
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time
from zipfile import ZipFile


BASE = Path(__file__).resolve().parents[1]
REPO = BASE.parents[3]
EXPECTED_LOCK = "f644d2c18e314f7ddc8733ddf4361fb8c72ac1315dc09ae36fe4e4b73cb13286"
MEMBER = "ETH_repo_upload/main_dataset_all_events.txt"
CAP = 100_000
RADII = tuple(map(D, ("0", ".01", ".02", ".05", ".1", ".2")))
VISIBILITIES = tuple(map(D, ("0", ".25", ".5", ".75", ".9", "1")))
OUTCOMES = ((1, 1), (1, -1), (-1, 1), (-1, -1))


def digest(path):
    result = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            result.update(chunk)
    return result.hexdigest()


def read(path):
    return json.loads(Path(path).read_text(), parse_float=D)


def git_hash(commit, name):
    value = subprocess.check_output(["git", "show", f"{commit}:{name}"], cwd=REPO)
    return hashlib.sha256(value).hexdigest()


def verify_binding():
    lock_path = BASE / "lock.json"
    assert digest(lock_path) == EXPECTED_LOCK
    lock = read(lock_path)
    assert len(lock["sources_sha256"]) == 34
    for name, expected in lock["sources_sha256"].items():
        assert digest(REPO / name) == expected, name
        assert git_hash(lock["code_commit"], name) == expected, name
    for name, commit in (("predict.py", lock["family_commit"]),
                         ("../delft-bell/statistics.py", lock["statistics_commit"])):
        path = (BASE / name).resolve()
        assert git_hash(commit, str(path.relative_to(REPO))) == digest(path)
    archive = REPO / lock["archive"]["local_path"]
    # Hash compressed bytes; do not decode other members or inspect their summaries.
    assert archive.stat().st_size == lock["archive"]["bytes"]
    assert digest(archive) == lock["archive"]["sha256"]
    access = read(BASE / "evidence/access.json")
    release = read(BASE / "evidence/custodian-release.json")
    assert git_hash(release["lock_commit"], str(lock_path.relative_to(REPO))) == EXPECTED_LOCK
    for record in (access, release):
        assert record["lock_sha256"] == EXPECTED_LOCK
        assert record["code_commit"] == lock["code_commit"]
    assert access["archive_sha256"] == lock["archive"]["sha256"]
    assert release["first_access_at"] == access["first_access_at"]
    for key in ("access_record", "results"):
        item = release[key]
        assert digest(REPO / item["path"]) == item["sha256"]
    assert release["invocations"] == 1 and release["exit_code"] == 0
    times = [lock["frozen_at"], release["execution_requested_at_utc"], access["first_access_at"],
             release["computed_at"], release["process_completion_observed_at_utc"],
             release["release_recorded_at_utc"]]
    parsed = [datetime.fromisoformat(value) for value in times]
    assert parsed == sorted(parsed) and parsed[-1] <= datetime.now(timezone.utc)
    return lock, archive, {"inputs_checked_current_and_commit": 34,
        "lock_sha256": EXPECTED_LOCK, "code_commit": lock["code_commit"],
        "lock_commit": release["lock_commit"], "archive_sha256": lock["archive"]["sha256"],
        "pipeline_first_access_at": access["first_access_at"], "ordered_time_chain": times,
        "custody_scope": "Byte/commit/time-chain consistency; first access means frozen pipeline access.",
        "access_sha256": digest(BASE / "evidence/access.json"),
        "release_sha256": digest(BASE / "evidence/custodian-release.json")}


def parse_event(raw, line):
    fields = raw.decode("utf-8").strip().split(",")
    assert len(fields) == 4, ("field_count", line)
    assert all(re.fullmatch(r"[+-]?\d+", item.strip()) for item in fields), ("integer", line)
    a, x, b, y = map(int, fields)
    assert a in (0, 1) and b in (0, 1), ("setting", line)
    assert x in (-1, 1) and y in (-1, 1), ("outcome", line)
    return 2 * a + b, 2 * (x == -1) + (y == -1)


def prefix_events(binary, prefix, cap=CAP):
    for line in range(1, 4):
        raw = binary.readline()
        assert raw, ("missing_header", line)
        prefix.update(raw)
    for ordinal in range(1, cap + 1):
        raw = binary.readline()
        if not raw:
            return
        prefix.update(raw)
        yield ordinal, parse_event(raw, ordinal + 3)
    # Deliberately no EOF probe or next-line read after the cap.


def log_mixture(values):
    largest = max(values)
    terms = [(value - largest).exp() for value in values if value - largest >= -200]
    return largest + sum(terms, D(0)).ln() - D(7).ln()


def fixed_tables():
    prediction = read(BASE / "predictions.json")
    assert [model["id"] for model in prediction["models"]] == ["ideal_source"]
    model = prediction["models"][0]
    assert model["alpha"] == D(".025")
    rows = [r for r in model["table"] if r["herald"] == 1]
    assert [(r["a"], r["b"]) for r in rows] == [(0, 0), (0, 1), (1, 0), (1, 1)]
    q = [r["probabilities"] for r in rows]
    nominal_error = D(0)
    for context, probabilities in enumerate(q):
        assert sum(probabilities) == 1 and min(probabilities) > 0
        correlation = (D(-1) if context == 2 else D(1)) / D(2).sqrt()
        for (x, y), probability in zip(OUTCOMES, probabilities):
            nominal_error = max(nominal_error, abs(probability - (1 + x*y*correlation)/4))
    assert nominal_error < D("1e-15")
    numerators = [[[((1-v)/4 + v*p).ln() for v in VISIBILITIES] for p in row] for row in q]
    denominators = [[[min(D(1), p+radius).ln() for radius in RADII] for p in row] for row in q]
    return model, numerators, denominators, nominal_error


def replay(archive):
    model, fixed, bounds, nominal_error = fixed_tables()
    counts = [[0] * 4 for _ in range(4)]
    totals = [0] * 4
    numerator_logs, denominator_logs = [D(0)] * 7, [D(0)] * 6
    maxima, at, final = [D(0)] * 6, [0] * 6, [D(0)] * 6
    prefix, n = hashlib.sha256(), 0
    started = time.monotonic()
    with ZipFile(archive) as container, container.open(MEMBER) as binary:
        for n, (context, outcome) in prefix_events(binary, prefix):
            kt = ((D(counts[context][outcome]) + D(".5")) / (totals[context] + 2)).ln()
            increments = fixed[context][outcome] + [kt]
            numerator_logs = [value + increment for value, increment in zip(numerator_logs, increments)]
            common = log_mixture(numerator_logs)
            for index, bound in enumerate(bounds[context][outcome]):
                denominator_logs[index] += bound
                final[index] = common - denominator_logs[index]
                if final[index] > maxima[index]:
                    maxima[index], at[index] = final[index], n
            counts[context][outcome] += 1
            totals[context] += 1
            if n % 20000 == 0:
                print(f"independent capped replay: {n} / {CAP}; {time.monotonic()-started:.1f}s", flush=True)
    assert n == CAP
    rows = [{"herald": 1, "a": c//2, "b": c%2, "n": sum(row), "outcome_counts": row}
            for c, row in enumerate(counts)]
    radii = [{"radius": str(radius), "max_log_e": str(maximum), "terminal_log_e": str(end),
              "anytime_p": str((-maximum).exp()), "terminal_e": str(end.exp()),
              "maximum_at_trial": peak, "maximum_at_source_line": peak+3 if peak else None,
              "reject_at_model_alpha": maximum >= -(model["alpha"].ln())}
             for radius, maximum, end, peak in zip(RADII, maxima, final, at)]
    return {"n_trials": n, "context_counts": rows, "radii": radii,
            "physical_lines": [4, CAP+3], "source_file": MEMBER, "consumed_prefix_sha256": prefix.hexdigest(),
            "prefixes_evaluated_per_radius": n+1, "nominal_probability_max_error": str(nominal_error)}


def compare(computed, lock):
    # Original results are decoded only after this independent replay has finished.
    report = read(BASE / "evidence/results.json")
    assert report["lock_sha256"] == EXPECTED_LOCK and report["code_commit"] == lock["code_commit"]
    assert report["trial_cap"] == CAP and report["first_trial"] == {"source_file": MEMBER, "source_line": 4}
    assert report["last_trial"] == {"source_file": MEMBER, "source_line": CAP+3}
    assert len(report["models"]) == 1
    model = report["models"][0]
    assert model["id"] == "ideal_source" and model["n_trials"] == computed["n_trials"]
    assert [r for r in model["context_counts"] if r["herald"] == 1] == computed["context_counts"]
    assert all(r["n"] == 0 and r["outcome_counts"] == [0]*4 for r in model["context_counts"] if r["herald"] == -1)
    assert model["outcome_order"] == [list(outcome) for outcome in OUTCOMES]
    discrepancies, underflows = [], []
    for original, independent in zip(model["radii"], computed["radii"], strict=True):
        assert original["radius"] == D(independent["radius"])
        assert original["reject_at_model_alpha"] == independent["reject_at_model_alpha"]
        assert not original["support_violation"]
        for key in ("max_log_e", "terminal_log_e"):
            error = abs(original[key] - D(independent[key]))
            assert error < D("1e-5"), (key, independent["radius"], str(error))
            discrepancies.append(error)
        for key in ("anytime_p", "terminal_e"):
            if original[key] == 0:
                exact = D(independent[key])
                assert 0 < exact < D(2) ** -1075
                underflows.append({"radius": independent["radius"], "field": key, "positive_decimal": str(exact)})
    verdict = "falsified" if computed["radii"][0]["reject_at_model_alpha"] else "not_falsified"
    assert model["verdict"] == verdict
    return {"counts_and_verdict_match": True, "point_verdict": verdict,
            "max_abs_log_difference": str(max(discrepancies)), "log_comparison_tolerance": "1e-5",
            "floating_underflows": underflows, "original_results_sha256": digest(BASE / "evidence/results.json")}


def self_check():
    from io import BytesIO
    data = BytesIO(b"h1\nh2\nh3\n0,1,1,-1\n1,-1,0,1\nDO NOT READ\n")
    got = list(prefix_events(data, hashlib.sha256(), cap=2))
    assert got == [(1, (1, 1)), (2, (2, 2))]
    assert data.tell() == len(b"h1\nh2\nh3\n0,1,1,-1\n1,-1,0,1\n")
    assert abs(log_mixture([D(0)]*7)) < D("1e-75")


def main():
    started = time.monotonic()
    with localcontext() as context:
        context.prec = 80
        self_check()
        lock, archive, binding = verify_binding()
        computed = replay(archive)
        comparison = compare(computed, lock)
        for name, expected in lock["sources_sha256"].items():
            assert digest(REPO / name) == expected, name
        result = {"schema": "independent-bell-decimal-recompute/v1", "status": "passed",
                  "created_at": datetime.now(timezone.utc).isoformat(), "decimal_precision": 80,
                  "independent_parser_and_statistics": True, "production_core_imported": False,
                  "only_designated_capped_member_decoded": True, "other_members_or_uncapped_summaries_opened": False,
                  "binding": binding, "recomputed": computed, "comparison": comparison,
                  "log_mixture_omission_bound": str(6*D(-200).exp()),
                  "claim": "Joint ideal source, nominal phase, preparation and readout conditions; no claim about an Euler residual.",
                  "script_sha256": digest(Path(__file__)), "seconds": round(time.monotonic()-started, 3)}
    destination = BASE / "evidence/independent-recompute.json"
    with destination.open("x") as stream:
        json.dump(result, stream, indent=2, allow_nan=False)
        stream.write("\n")
    print(json.dumps({"status": result["status"], "max_abs_log_difference": comparison["max_abs_log_difference"],
                      "evidence_sha256": digest(destination), "seconds": result["seconds"]}), flush=True)


if __name__ == "__main__":
    main()
