"""Frozen full-record consumer. No fitting, paired event decoding or physical action inference."""
import argparse
import json
import subprocess
from pathlib import Path

import history_feed
import history_feed_independent

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[5]
SCIENCE = tuple(BASE / name for name in (
    "criterion-hr0001.md", "criterion-hr0001.1.md", "history_feed.py",
    "history_feed_independent.py", "history_run.py", "test_history_feed.py"))
PAID = BASE.parent / "primary-first-mu0001.1.json"
PARSERS = (BASE.parent / "schema.py", BASE.parent / "invariant_independent.py")


def freeze_bindings():
    history_feed.validate_parser_binding()
    history_feed_independent.validate_parser_binding()
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    result = []
    for path in (*SCIENCE, PAID, *PARSERS):
        relative = str(path.relative_to(ROOT))
        raw = path.read_bytes()
        frozen = subprocess.check_output(["git", "show", f"{head}:{relative}"], cwd=ROOT)
        if frozen != raw:
            raise ValueError(f"unfrozen source: {relative}")
        result.append({"path": relative, "sha256": history_feed.schema.sha256(raw)})
    return head, result


def execute(directory, output):
    head, bindings = freeze_bindings()
    output = Path(output)
    attempt = output.with_name(output.stem + "-attempt.json")
    if output.exists() or attempt.exists():
        raise FileExistsError("first history consumption already recorded")
    with attempt.open("x", encoding="utf-8") as destination:
        json.dump({"schema": "bell-history-consumption-attempt/v1", "version": "hr0001.1",
                   "execution_head": head, "source_bindings": bindings}, destination, indent=2)
        destination.write("\n")
    result = {"schema": "bell-public-record-history/v1", "version": "hr0001.1",
              "execution_head": head, "source_bindings": bindings,
              "controller_advance": False, "source": "positiveSmoothUnifiedSource",
              "root_visit": 10, "current_tick": 16, "next_tick": 17,
              "pair_csv_decoded": False, "statistics_replayed": False,
              "physical_action_inferred_from_record_order": False,
              "full_history_nonrecoverability_certified": False,
              "actual_hardware_parameters_uniquely_recovered": False}
    try:
        paid = json.loads(PAID.read_text(encoding="utf-8"))
        primary = [history.summary() for history in history_feed.load_histories(directory, paid)]
        independent = list(history_feed_independent.load_summaries(directory, paid))
        if primary != independent or not all(item["every_record_recovered"] for item in primary):
            raise ValueError("independent full record observer mismatch")
        result.update(status="complete_public_record_history_connected", primary=primary,
                      independent=independent, public_records=sum(item["records"] for item in primary),
                      all_available_local_record_fields_preserved=True)
    except Exception as error:
        result.update(status="rejected", error_type=type(error).__name__, error=str(error))
        with output.open("x", encoding="utf-8") as destination:
            json.dump(result, destination, indent=2, sort_keys=True)
            destination.write("\n")
        raise
    with output.open("x", encoding="utf-8") as destination:
        json.dump(result, destination, indent=2, sort_keys=True)
        destination.write("\n")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--directory", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    receipt = execute(args.directory, args.output)
    print(json.dumps({"status": receipt["status"], "public_records": receipt["public_records"]}))
