"""Read-only consumption of the frozen complete successor-clock observation table."""
import argparse
from collections import Counter
import json
from pathlib import Path
import subprocess

import history_verify as history

BASE = Path(__file__).resolve().parent
FIRST = BASE / "clock-first-cl0001.json"
ATTEMPT = BASE / "clock-first-cl0001-attempt.json"
CERTIFICATE = BASE / "clock-verification-cl0001.json"
SCHEMA = "stage10-munich-successor-clock-evidence/v1"
CUTS = list(map(str, (100, 500, 1000, 2000, 3000, 5000, 10000, 20000,
                     40000, 80000, 160000, 320000, 640000)))
SCIENCE = tuple(BASE / name for name in ("criterion-cl0001.md", "clock_observation.py",
    "clock_observation_independent.py", "clock_run.py", "test_clock_observation.py"))
DEPENDENCIES = (BASE / "history_feed.py", BASE / "history_feed_independent.py",
                BASE.parent / "schema.py", BASE.parent / "invariant_independent.py", history.PAID)
STATUSES = {"positive", "zero_clock_retained", "negative_clock_retained",
            "invalid_clock_retained", "right_censored"}


def counts(values, expected=None):
    history.require(isinstance(values, dict) and set(values) <= STATUSES and
                    all(type(value) is int and value >= 0 for value in values.values()), "clock statuses")
    if expected is not None:
        history.require(sum(values.values()) == expected, "clock status conservation")
    return Counter(values)


def cdf(values, statuses):
    valid = statuses.get("positive", 0) + statuses.get("zero_clock_retained", 0)
    history.require(isinstance(values, list) and len(values) == len(CUTS) and
                    all(type(value) is int and 0 <= value <= valid for value in values) and
                    values == sorted(values), "clock cumulative counts")


def check_local(table, original):
    history.require(table["records"] == original["records"] and table["cuts_ms"] == CUTS,
                    "clock local inventory")
    aggregate, keys = Counter(), set()
    for group in table["groups"]:
        key = json.dumps((group["current"], group["following"]), separators=(",", ":"))
        history.require(key not in keys and len(group["current"]) == 6 and
                        (group["following"] is None or len(group["following"]) == 6), "clock local context")
        keys.add(key)
        status = counts(group["statuses"], group["records"])
        cdf(group["cdf_counts"], status)
        aggregate.update(status)
    history.require(aggregate == counts(table["statuses"], table["records"]), "clock local conservation")
    history.require(aggregate["right_censored"] == 1, "clock last original row")


def check_pair(table, original):
    history.require(table["pairs"] == original["trials"], "clock pair inventory")
    history.require(table["cuts_ms"] == CUTS and table["token_dictionaries"] == original["token_dictionaries"],
                    "clock pair dictionary")
    total, aggregate, keys = 0, Counter(), set()
    for cell in table["cells"]:
        key = tuple(cell["context_outcome"])
        history.require(len(key) == 5 and all(type(value) is int and value in (0, 1) for value in key)
                        and key not in keys, "clock pair context")
        keys.add(key)
        total += cell["records"]
        for role in ("local1", "local2"):
            status = counts(cell[role + "_statuses"], cell["records"])
            cdf(cell[role + "_cdf_counts"], status)
            aggregate.update({role + ":" + name: value for name, value in status.items()})
    history.require(total == table["pairs"] and dict(aggregate) == table["statuses"], "clock pair conservation")


def generate():
    source = history.consume()
    first = json.loads(history.frozen(FIRST))
    attempt = json.loads(history.frozen(ATTEMPT))
    paid = json.loads(history.frozen(history.PAID))
    history.require(first.get("schema") == "bell-public-clock-domain-table/v1" and
                    first.get("version") == "cl0001" and first.get("evidence_valid") is True and
                    first.get("status") == "complete_clock_domain_table_generated" and
                    first.get("independent_full_table_agreement") is True, "clock first identity")
    history.require(attempt.get("schema") == "bell-clock-consumption-attempt/v1" and
                    attempt.get("version") == first["version"] and
                    attempt.get("execution_head") == first.get("execution_head"), "clock attempt identity")
    expected = [history.binding(path) for path in SCIENCE + DEPENDENCIES]
    history.require(first.get("source_bindings") == attempt.get("source_bindings") == expected, "clock source bindings")
    for path in SCIENCE + DEPENDENCIES:
        history.frozen(path, first["execution_head"])
    history.require(subprocess.run(["git", "merge-base", "--is-ancestor", first["execution_head"], "HEAD"],
                                   cwd=history.ROOT, capture_output=True).returncode == 0, "clock freeze ancestry")
    for key in ("source", "root_visit", "current_tick", "next_tick"):
        history.require(first.get(key) == source[key], "clock original occurrence")
    for key in ("controller_advance", "source_clock_record_square_certified",
                "physical_action_inferred_from_record_order", "gap_used_as_loss_label",
                "actual_hardware_uniquely_identified", "new_inferential_confidence_budget_spent"):
        history.require(first.get(key) is False, "clock scope promoted: " + key)
    for key in ("old_statistical_prefixes_replayed", "new_atomic_forward_executions"):
        history.require(type(first.get(key)) is int and first[key] == 0, "clock execution scope")
    records = json.loads(history.frozen(history.FIRST))["primary"]
    expected_locals = {(item["run"], item["role"]): item for item in records}
    tables = first["local_clock_tables"]
    history.require(len(tables) == 4 and {(item["run"], item["role"]) for item in tables} == set(expected_locals),
                    "clock local addresses")
    for table in tables:
        check_local(table, expected_locals[table["run"], table["role"]])
    runs = {item["run"]: item for item in paid["runs"]}
    pairs = first["pair_clock_tables"]
    history.require(len(pairs) == 2 and {item["run"] for item in pairs} == set(runs), "clock original run addresses")
    for table in pairs:
        check_pair(table, runs[table["run"]])
    history.require(first["public_records"] == sum(item["records"] for item in tables) == source["public_records"] and
                    first["paired_current_records"] == sum(item["pairs"] for item in pairs), "clock total conservation")
    return {"schema": SCHEMA, "version": "cl0001", "evidence_valid": True,
            "status": "certified_complete_public_successor_clock_table",
            "complete_public_successor_clock_history_connected": True,
            "same_original_source_history_consumer": True,
            "independent_full_table_agreement": True,
            "source": source["source"], "root_visit": 10, "current_tick": 16, "next_tick": 17,
            "public_records": first["public_records"], "paired_current_records": first["paired_current_records"],
            "clock_views_per_role": len(CUTS), "pair_clock_joint_distribution_preserved": False,
            "source_clock_record_square_certified": False, "actual_hardware_uniquely_identified": False,
            "full_history_nonrecoverability_certified": False, "controller_advance": False,
            "trial_events_read_at_intake": 0, "new_statistical_executions_at_intake": 0,
            "source_bindings": [history.binding(path) for path in
                                (Path(__file__).resolve(), FIRST, ATTEMPT, history.BASE / "history-verification.json")]}


def consume(certificate=None):
    expected = generate()
    path = CERTIFICATE if certificate is None else Path(certificate)
    history.require(expected == json.loads(path.read_text(encoding="utf-8")), "clock certificate changed")
    return expected


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--certificate", type=Path)
    args = parser.parse_args()
    try:
        result = consume(args.certificate) if args.check_only else generate()
        if not args.check_only:
            history.require(args.certificate is None, "clock override is intake only")
            with CERTIFICATE.open("x", encoding="utf-8") as output:
                json.dump(result, output, indent=2, sort_keys=True)
                output.write("\n")
        print(json.dumps(result, sort_keys=True))
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(json.dumps({"schema": SCHEMA, "evidence_valid": False, "reason": str(error)}))
        raise SystemExit(1)
