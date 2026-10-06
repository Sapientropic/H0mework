"""Frozen clock-domain-table generation; no inferential or hardware verdict."""
import argparse
import io
import json
from pathlib import Path
import subprocess
from zipfile import ZipFile

import clock_observation as primary
import clock_observation_independent as independent
import history_feed as history
import history_feed_independent as independent_history

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[5]
PAID = BASE.parent / "primary-first-mu0001.1.json"
SCIENCE = tuple(BASE / name for name in ("criterion-cl0001.md", "clock_observation.py",
    "clock_observation_independent.py", "clock_run.py", "test_clock_observation.py"))
DEPENDENCIES = (BASE / "history_feed.py", BASE / "history_feed_independent.py",
                BASE.parent / "schema.py", BASE.parent / "invariant_independent.py", PAID)


def frozen_bindings():
    history.validate_parser_binding()
    independent_history.validate_parser_binding()
    commit = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    bindings = []
    for path in SCIENCE + DEPENDENCIES:
        name = str(path.relative_to(ROOT))
        raw = path.read_bytes()
        if raw != subprocess.check_output(["git", "show", f"{commit}:{name}"], cwd=ROOT):
            raise ValueError("unfrozen clock source: " + name)
        bindings.append({"path": name, "sha256": history.schema.sha256(raw)})
    return commit, bindings


def exclusive(path, data):
    with path.open("x", encoding="utf-8") as output:
        json.dump(data, output, ensure_ascii=False, indent=2, sort_keys=True)
        output.write("\n")


def execute(directory, output):
    commit, bindings = frozen_bindings()
    output = Path(output)
    attempt = output.with_name(output.stem + "-attempt.json")
    if output.exists() or attempt.exists():
        raise FileExistsError("clock first consumption exists")
    exclusive(attempt, {"schema": "bell-clock-consumption-attempt/v1", "version": "cl0001",
                        "execution_head": commit, "source_bindings": bindings})
    receipt = {"schema": "bell-public-clock-domain-table/v1", "version": "cl0001",
               "execution_head": commit, "source_bindings": bindings,
               "source": "positiveSmoothUnifiedSource", "root_visit": 10,
               "current_tick": 16, "next_tick": 17, "controller_advance": False,
               "source_clock_record_square_certified": False,
               "physical_action_inferred_from_record_order": False,
               "gap_used_as_loss_label": False, "actual_hardware_uniquely_identified": False,
               "new_inferential_confidence_budget_spent": False,
               "old_statistical_prefixes_replayed": 0, "new_atomic_forward_executions": 0}
    try:
        paid = json.loads(PAID.read_text(encoding="utf-8"))
        paid_runs = {item["run"]: item["local_audit"] for item in paid["runs"]}
        histories = history.load_histories(directory, paid)
        history_index = {(item.run, item.role): item for item in histories}
        summaries, checked_summaries, pairs, checked_pairs = [], [], [], []
        for spec, identity in zip(history.schema.ARCHIVES, independent_history.parser.ARCHIVE_IDENTITIES):
            raw = (Path(directory) / spec.name).read_bytes()
            history.schema.require(history.schema.sha256(raw) == spec.sha256, "clock_archive_identity")
            with ZipFile(io.BytesIO(raw)) as archive:
                raws = [archive.read(getattr(spec, role)) for role in ("local1", "local2", "pairs")]
            admitted = history.schema.admit_run_bytes(spec.run, *raws)
            checked = independent_history.parser.archive_run(raw, identity)
            history.schema.require(admitted.audit == checked.audit == paid_runs[spec.run], "clock_paid_join_changed")
            parsed = []
            for role, payload in zip(("local1", "local2"), raws):
                original = history_index[spec.run, role]
                rows = independent_history.observe_bytes(payload, spec.run, role)
                history.schema.require(rows == original.observations, "clock_full_history_changed")
                summaries.append(primary.summarize(original))
                checked_summaries.append(independent.summarize(spec.run, role, rows, original.paired_rows))
                parsed.append((rows, original.paired_rows))
            pairs.append(primary.pair_summary(history_index[spec.run, "local1"], history_index[spec.run, "local2"], admitted))
            checked_pairs.append(independent.pair_summary(spec.run, parsed[0][0], parsed[1][0], parsed[0][1], parsed[1][1], checked))
        history.schema.require(summaries == checked_summaries and pairs == checked_pairs, "clock_observer_cross_mismatch")
        receipt.update(status="complete_clock_domain_table_generated", evidence_valid=True,
                       public_records=sum(item["records"] for item in summaries),
                       paired_current_records=sum(item["pairs"] for item in pairs),
                       local_clock_tables=summaries, pair_clock_tables=pairs,
                       independent_full_table_agreement=True)
    except Exception as error:
        receipt.update(status="rejected", evidence_valid=False, error_type=type(error).__name__, error=str(error))
        exclusive(output, receipt)
        raise
    exclusive(output, receipt)
    return receipt


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    result = execute(args.directory, args.output)
    print(json.dumps({"status": result["status"], "public_records": result["public_records"],
                      "paired_current_records": result["paired_current_records"]}))
