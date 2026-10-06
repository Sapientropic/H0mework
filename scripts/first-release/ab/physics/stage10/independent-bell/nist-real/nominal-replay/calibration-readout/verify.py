"""Certification intake for the frozen source-count calibration readout."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import queue
import re
import subprocess
import tempfile
import threading
import time
from fractions import Fraction as F

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
VERSION = "p23-calibration-readout-cal0001"
SCHEMA = "p23-calibration-readout-verification/v1"
FREEZE = "d9ead286cf6f3fb9051e4cb6aa235603e115dc97"
LAW_FREEZE = "829534f0e1eace805ce60918880041d5d9efa8b8"
LAW_SHA = "0944bbc767afe4e1456613ad36caeaf0f8c90402839356a78aa015078c204e2d"
COMPARISON_FREEZE = "51f246f406c83e3e040695ae16e35db146f75172"
FIRST = {"independent_count.json": "0858761ce5840aa1ed1a7dc09f37604a7a1ed08b2a97aad4d5bb3a35dac2bf54",
         "calibration.json": "547ebf134776b1c6707e79929579dcb58047f70fa10d44fb047cd568639408a3"}
FLAGS = ("calibration_preparation_identified", "calibration_ports_identified", "calibration_pump_identified",
         "background_subtraction_identified", "source_mapping_identified", "publication_configuration_identified", "production_admitted")
TRUTH = ["source_generated_distinct_pair_quantities", "inclusive_loss_source_PGF",
         "matched_single_pol_single_pulse_signal_only_exact_Klyshko", "matched_increase_zero_to_two_mean",
         "zero_herald_option_undefined"]
CHAIN = (HERE.parent/"gaussian-window/GaussianSource.lean", HERE/"CalibrationLaw.lean", HERE/"CalibrationCertification.lean")


def require(value, reason):
    if not value:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def relative(path):
    return Path(path).relative_to(ROOT).as_posix()


def load(path):
    def reject_constant(value):
        raise ValueError("nonfinite_json:"+value)
    return json.loads(Path(path).read_text(), parse_constant=reject_constant)


def frozen(path, commit=None):
    path = Path(path)
    name = relative(path)
    if commit is None:
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", name], cwd=ROOT, text=True).strip()
    require(bool(commit), "uncommitted_audit_source:"+name)
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True, capture_output=True)
    require(subprocess.check_output(["git", "show", commit+":"+name], cwd=ROOT) == path.read_bytes(), "frozen_source_changed:"+name)
    return {"commit": commit, "sha256": digest(path)}


def inputs():
    for name in ("criterion.md", "sources.json"):
        frozen(HERE/name, FREEZE)
    spec = load(HERE/"sources.json")
    require(spec["version"] == VERSION and all(spec[k] is False for k in FLAGS), "calibration_identity_changed")
    require(spec["private_optimizer_input_required"] is False and type(spec["bell_event_files_read"]) is int and spec["bell_event_files_read"] == 0,
            "invalid_calibration_source_role")
    require(spec["eta_probability_half_width"] == "0.003" and spec["public_visibility_preparation"] == "maximally_entangled"
            and spec["public_visibility_uncertainty_role"] == "k=1 standard deviation", "public_calibration_role_or_unit_changed")
    bindings = {}
    for row in spec["inputs"]:
        path = (ROOT/row["path"]).resolve()
        require(path.is_relative_to(ROOT) and row["path"] not in bindings and digest(path) == row["sha256"], "old_source_binding_changed")
        bindings[row["path"]] = row["sha256"]
    require(digest(HERE/"CalibrationLaw.lean") == LAW_SHA, "calibration_law_changed")
    frozen(HERE/"CalibrationLaw.lean", LAW_FREEZE)
    for name in ("criterion.md", "sources.json", "CalibrationLaw.lean", "CalibrationCertification.lean", "verify.py", "tests.py"):
        bindings[relative(HERE/name)] = digest(HERE/name)
    freezes = {relative(path): frozen(path) for path in (*CHAIN, HERE/"verify.py", HERE/"tests.py")}
    return bindings, freezes


def lsp_check(project, env, paths):
    process = subprocess.Popen(["lean", "--server"], cwd=project, env=env,
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    inbox = queue.Queue()
    def reader():
        while header := process.stdout.readline():
            if not header.startswith(b"Content-Length:"):
                continue
            length = int(header.split(b":")[1])
            while process.stdout.readline() not in (b"\r\n", b"\n", b""):
                pass
            inbox.put(json.loads(process.stdout.read(length)))
    threading.Thread(target=reader, daemon=True).start()
    def send(message):
        body = json.dumps(dict(jsonrpc="2.0", **message)).encode()
        process.stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode()+body)
        process.stdin.flush()
    def until(predicate):
        deadline = time.monotonic()+45
        while time.monotonic() < deadline:
            try:
                item = inbox.get(timeout=1)
            except queue.Empty:
                require(process.poll() is None, "task_owned_LSP_exited")
                continue
            if predicate(item):
                return
        raise TimeoutError("task_owned_LSP_timeout")
    try:
        send({"id": 1, "method": "initialize", "params": {"processId": os.getpid(), "rootUri": project.as_uri(), "capabilities": {}}})
        until(lambda item: item.get("id") == 1)
        send({"method": "initialized", "params": {}})
        records = []
        for index, path in enumerate(paths, 2):
            uri = path.as_uri()
            send({"method": "textDocument/didOpen", "params": {"textDocument": {"uri": uri, "languageId": "lean4", "version": 1, "text": path.read_text()}}})
            send({"id": index, "method": "textDocument/documentSymbol", "params": {"textDocument": {"uri": uri}}})
            state = {"response": None, "idle": False, "diagnostics": None}
            def ready(item):
                if item.get("id") == index:
                    state["response"] = item
                params = item.get("params", {})
                if item.get("method") == "$/lean/fileProgress" and params.get("textDocument", {}).get("uri") == uri:
                    state["idle"] = not params.get("processing", [])
                if item.get("method") == "textDocument/publishDiagnostics" and params.get("uri") == uri:
                    state["diagnostics"] = params["diagnostics"]
                return state["response"] is not None and state["idle"] and state["diagnostics"] is not None
            until(ready)
            require("error" not in state["response"] and not [d for d in state["diagnostics"] if d.get("severity", 1) <= 2], "LSP_calibration_diagnostics")
            records.append({"file": path.name, "errors": 0, "warnings": 0, "symbol_count": len(state["response"].get("result") or []),
                            "method": "task-owned lean --server; documentSymbol, idle fileProgress, published diagnostics"})
            send({"method": "textDocument/didClose", "params": {"textDocument": {"uri": uri}}})
        return records
    finally:
        process.terminate()
        try:
            process.wait(timeout=5)
        except subprocess.TimeoutExpired:
            process.kill(); process.wait()


def fresh_compilation():
    bindings, freezes = inputs()
    project = ROOT/"Lean"
    env = json.loads(subprocess.check_output(["lake", "env", "python3", "-c", "import json,os; print(json.dumps(dict(os.environ)))"], cwd=project, text=True))
    checks = []
    with tempfile.TemporaryDirectory(prefix="p23-calibration-certify-") as temporary:
        env["LEAN_PATH"] = temporary+os.pathsep+env.get("LEAN_PATH", "")
        for path in CHAIN:
            command = ["lean", "--trust=0", "-DwarningAsError=true", "--root="+str(path.parent), "-o", str(Path(temporary)/(path.stem+".olean")), str(path)]
            run = subprocess.run(command, cwd=project, env=env, text=True, capture_output=True, timeout=120)
            shown = command.copy(); shown[5] = "${fresh_olean}/"+path.stem+".olean"
            checks.append({"source": relative(path), "command": shown, "exit_code": run.returncode, "stdout": run.stdout, "stderr": run.stderr})
            require(run.returncode == 0, "focused_calibration_compile_failed:"+path.name+":"+run.stdout+run.stderr)
        lsp = lsp_check(project, env, list(CHAIN))
    require(all(digest(ROOT/name) == row["sha256"] for name, row in freezes.items()), "source_changed_during_compilation")
    match = re.search(r"CALIBRATION_CERTIFIED declarations=(\d+) nodes=(\d+) required=(\d+) primitive=(\d+)", checks[-1]["stdout"])
    require(match is not None, "missing_source_closure_axiom_audit")
    counts = dict(zip(("candidate_declarations", "dependency_nodes", "required_nodes", "primitive_nodes"), map(int, match.groups())))
    return {"fresh_source_compilation": True, "trust_level": 0, "warning_as_error": True, "commands": checks, "lsp": lsp}, counts, bindings, freezes


def exact(value):
    return F(value["exact"])


def endpoints(interval):
    return F(interval["exact_lower"]), F(interval["exact_upper"])


def packet_key(packet):
    return tuple(tuple(exact(x) if isinstance(x, dict) else F(x) for x in packet[key]) for key in ("geometric_ratio", "transmission_A", "transmission_B"))


def numeric_audit():
    bindings = {}
    reports = {}
    for name, sha in FIRST.items():
        path = HERE/name
        require(digest(path) == sha, "first_scientific_snapshot_changed:"+name)
        reports[name] = load(path); bindings[relative(path)] = sha
    independent, primary = reports["independent_count.json"], reports["calibration.json"]
    require(independent["status"] == "PASS" and primary["status"] == "source_generated_calibration_readout", "scientific_receipt_failed")
    for name, report, sha_key in (("calibration.py", primary, "sha256"), ("independent_count.py", independent, "program_sha256")):
        freeze = frozen(HERE/name, report["executable_freeze"]["commit"])
        require(freeze["sha256"] == report["executable_freeze"][sha_key], "scientific_program_binding_changed")
        bindings[relative(HERE/name)] = freeze["sha256"]
    comparison_freeze = frozen(HERE/"comparison.py", COMPARISON_FREEZE)
    comparison = load(HERE/"independent-comparison.json")
    require(comparison["executable_freeze"]["commit"] == COMPARISON_FREEZE and comparison["executable_freeze"]["program_sha256"] == comparison_freeze["sha256"], "posthoc_comparison_not_bound")
    bindings[relative(HERE/"comparison.py")] = comparison_freeze["sha256"]
    bindings[relative(HERE/"independent-comparison.json")] = digest(HERE/"independent-comparison.json")
    require(all(report.get(k) is False for report in (primary, independent, comparison) for k in FLAGS), "unbound_calibration_role_promoted")
    require(all(report.get("actual_calibration_failure_claimed", False) is False for report in (primary, independent, comparison)), "actual_calibration_failure_claimed")
    require(comparison["no_calibration_branch_selected"] is True and comparison["scientific_receipts_preserved_byte_identical"] is True, "calibration_branch_selected")
    require(primary["public_q"]["used_to_fit_source"] is False and independent["public_q"]["acceptance_interval"] is None, "public_q_used_as_fit_or_tolerance")
    require(all(report["other_implementation_output_used_as_input"] is False for report in (primary, independent)), "independent_probability_input_changed")
    inputs_map, _ = inputs()
    science_paths = {row["path"] for row in load(HERE/"sources.json")["inputs"]}
    science_paths.update(relative(HERE/name) for name in ("criterion.md", "sources.json"))
    for report in (primary, independent):
        require(report["version"] == VERSION and all(report["bindings"].get(k) == inputs_map[k] for k in science_paths), "scientific_binding_changed")
    source_rows = {row["preparation"]: row for row in independent["preparations"]}
    require(set(source_rows) == {"dual_pol", "pure_H", "pure_V"}, "calibration_preparations_incomplete")
    primary_rows = {(packet_key(row["source_parameters"]), row["window_pulses"], row["background_model"]): row for row in primary["branches"]}
    expected_ids = {f"{prep}/N{window}/{background}" for prep in source_rows for window in (1, 5) for background in ("signal_only", "independent_OR")}
    require(len(primary_rows) == len(primary["branches"]) == len(independent["branches"]) == 12 and {row["case_id"] for row in independent["branches"]} == expected_ids, "twelve_branch_selection_or_duplication")
    rates = ratios = matched = 0
    visited = set()
    eta_bounds = {"alice": (F(".744"), F(".750")), "bob": (F(".753"), F(".759"))}
    quantity_names = {"pair_at_least_one": "at_least_one", "exactly_one": "exactly_one", "mean_pair": "mean_pair"}
    for row in independent["branches"]:
        source = source_rows[row["preparation"]]
        key = (packet_key(source["source_parameters"]), row["window_pulses"], row["background_model"])
        require(key in primary_rows and key not in visited and row["conditional_public_eta"]["alice"]["calibration_identity_identified"] is False and row["conditional_public_eta"]["bob"]["calibration_identity_identified"] is False, "branch_source_or_identity_changed")
        visited.add(key); other = primary_rows[key]
        h, v = key[0][0]
        generated = {"pair_at_least_one": h+v-h*v, "exactly_one": (1-h)*(1-v)*(h+v), "mean_pair": h/(1-h)+v/(1-v)}
        for name, primary_name in quantity_names.items():
            require(exact(source["source_pair_readouts"][name]) == exact(other["pair_quantities_per_pulse"][primary_name]) == generated[name], "pair_quantities_conflated")
        for name in ("sA", "sB", "j"):
            lo, hi = endpoints(row["rates"][name]); value = exact(other["probabilities"][name])
            require(0 <= lo <= value <= hi <= 1, "primary_rate_outside_independent_tail")
            rates += 1
        for side, party, herald in (("alice", "Alice", "sB"), ("bob", "Bob", "sA")):
            own, point = row["Klyshko"][side], other["Klyshko"][party]
            require(own["status"] == "DEFINED" and point["status"] == "defined", "positive_herald_not_defined")
            lo, hi = endpoints(own["interval"]); value = exact(point["value"])
            require(0 <= lo <= value <= hi <= 1 and value == exact(other["probabilities"]["j"])/exact(other["probabilities"][herald]), "primary_ratio_outside_independent_tail")
            eta_lo, eta_hi = eta_bounds[side]
            intersects = max(lo, eta_lo) <= min(hi, eta_hi)
            eta = row["conditional_public_eta"][side]
            require(tuple(map(F, eta["public_interval"])) == eta_bounds[side] and eta["status"] == ("INTERSECTS" if intersects else "DISJOINT"),
                    "conditional_public_eta_role_changed")
            ratios += 1
            if "matched_single_polarization" in row:
                m = row["matched_single_polarization"]
                require(m[side]["status"] == "DEFINED" and exact(m[side]["K"]) == value and m[side]["bound_passed"] is True and m[side]["number_enclosed"] is True, "matched_calibration_not_source_generated")
                matched += 1
    require(len(visited) == 12 and (rates, ratios, matched) == (36, 24, 4), "calibration_consumer_coverage_incomplete")
    require(independent["controls"]["case_count"] == 60 and independent["controls"]["passed"] is True and all(independent["controls"]["checks"].values()) and primary["controls"]["case_count"] == 28 and all(primary["controls"]["checks"].values()), "source_count_controls_failed")
    require(independent["controls"]["checks"]["zero_herald_explicitly_undefined"] is True and independent["controls"]["checks"]["zero_source_not_fake_transmission_efficiency"] is True and primary["controls"]["checks"]["vacuum_herald_is_undefined"] is True, "zero_herald_fake_efficiency")
    require(comparison["status"] == "PASS" and comparison["errors"] == [] and all(comparison["shared_input_identity"].values()) and all(comparison["checks"].values()), "posthoc_comparison_failed")
    text = (HERE.parent/"shalm2015-channel-inputs.txt").read_text()
    rows = re.findall(r"(\d+(?:\.\d+)?)\s+\+-\s+(\d+(?:\.\d+)?)\s*%\s*\((Alice|Bob)\)", text)
    require(len(rows) == 2 and {r[2] for r in rows} == {"Alice", "Bob"} and all(F(width)/100 == F(".003") for _, width, _ in rows) and load(HERE/"sources.json")["eta_probability_half_width"] == "0.003", "public_efficiency_probability_unit_changed")
    return {"first_scientific_snapshots_byte_identical": True, "twelve_branches_bijective": True,
            "exact_primary_rates_enclosed": rates, "exact_primary_Klyshko_enclosed": ratios, "matched_exact_conditional_efficiencies": matched,
            "control_counts": {"primary": 28, "independent": 60}, "zero_herald_explicitly_undefined": True,
            "public_efficiency_probability_half_width": "0.003", "no_calibration_branch_selected": True,
            "pair_quantities_distinct": True, "bindings": bindings}


def certify():
    focused, counts, bindings, freezes = fresh_compilation()
    numeric = numeric_audit()
    audit = {**counts, "source_count_PGF_loss_and_matched_consumer_in_closure": True,
             "target_in_primitive": False, "operational_root_in_closure": False}
    report = {"schema": "p23-calibration-readout-lean-certification/v1", "version": VERSION, "status": "certified", "phase": "lean-certify",
              "criterion_freeze": {"commit": FREEZE, "criterion_sha256": digest(HERE/"criterion.md"), "sources_sha256": digest(HERE/"sources.json")},
              "kernel_claims": TRUTH, "authorized_axioms": ["propext", "Classical.choice", "Quot.sound"], "source_audit": audit,
              "focused_verification": focused, "execution_source_freezes": freezes, "bindings": bindings, "numeric_audit": numeric,
              "actual_calibration_failure_claimed": False, "no_calibration_branch_selected": True, **{k: False for k in FLAGS},
              "scope": "Source-count calibration; exact matched single-pol/single-pulse/signal-only Klyshko. No public calibration identity or full-Fock visibility/window Born theorem assigned."}
    (HERE/"certification.json").write_text(json.dumps(report, indent=2, allow_nan=False)+"\n")
    return report


def assess(report_dir=None, *, enabled=True):
    base = {"schema": SCHEMA, "version": VERSION, "evidence_valid": False, **{k: False for k in FLAGS},
            "actual_calibration_failure_claimed": False, "no_calibration_branch_selected": True,
            "private_optimizer_input_required": False, "bell_event_files_read": 0}
    if not enabled:
        return {**base, "status": "disabled_by_override"}
    try:
        bindings, freezes = inputs()
        directory = HERE if report_dir is None else Path(report_dir)
        authoritative = frozen(HERE/"certification.json")
        require(digest(directory/"certification.json") == authoritative["sha256"], "calibration_certificate_not_authoritative")
        receipt = load(directory/"certification.json")
        require(receipt["schema"] == "p23-calibration-readout-lean-certification/v1" and receipt["version"] == VERSION and receipt["status"] == "certified" and receipt["phase"] == "lean-certify" and receipt["bindings"] == bindings,
                "invalid_calibration_certificate")
        require(receipt["kernel_claims"] == TRUTH and receipt["authorized_axioms"] == ["propext", "Classical.choice", "Quot.sound"] and all(receipt[k] is False for k in FLAGS) and receipt["actual_calibration_failure_claimed"] is False and receipt["no_calibration_branch_selected"] is True, "calibration_scope_promoted")
        require(receipt["criterion_freeze"] == {"commit": FREEZE, "criterion_sha256": digest(HERE/"criterion.md"), "sources_sha256": digest(HERE/"sources.json")}, "calibration_criterion_changed")
        focused = receipt["focused_verification"]
        require(focused["fresh_source_compilation"] is True and type(focused["trust_level"]) is int and focused["trust_level"] == 0 and focused["warning_as_error"] is True and [row["source"] for row in focused["commands"]] == [relative(path) for path in CHAIN] and all(type(row["exit_code"]) is int and row["exit_code"] == 0 for row in focused["commands"]) and [row["file"] for row in focused["lsp"]] == [path.name for path in CHAIN] and all(row["errors"] == row["warnings"] == 0 for row in focused["lsp"]), "invalid_fresh_calibration_receipt")
        require(receipt["source_audit"]["source_count_PGF_loss_and_matched_consumer_in_closure"] is True and receipt["source_audit"]["target_in_primitive"] is False and receipt["source_audit"]["operational_root_in_closure"] is False, "invalid_calibration_closure_audit")
        numeric = numeric_audit()
        require(receipt["numeric_audit"] == numeric, "calibration_numeric_audit_changed")
        return {**base, "status": "verified", "evidence_valid": True, "kernel_claims": TRUTH, "source_audit": receipt["source_audit"],
                "numeric_audit": numeric, "fresh_source_compilation": True, "criterion_freeze": receipt["criterion_freeze"],
                "execution_source_freezes": freezes, "certificate_freeze": authoritative,
                "bindings": {**bindings, **numeric["bindings"], "certification.json": authoritative["sha256"]}, "scope": receipt["scope"]}
    except FileNotFoundError as error:
        return {**base, "status": "missing_calibration_evidence", "reason": str(error)}
    except (ValueError, KeyError, TypeError, AttributeError, ArithmeticError, OSError, subprocess.SubprocessError) as error:
        return {**base, "status": "invalid_calibration_evidence", "reason": str(error)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true")
    parser.add_argument("--directory", type=Path)
    parser.add_argument("--disabled", action="store_true")
    parser.add_argument("--certify", action="store_true")
    args = parser.parse_args()
    result = certify() if args.certify else assess(args.directory, enabled=not args.disabled)
    print(json.dumps(result, indent=2, allow_nan=False))
    return 0 if result["status"] in ("verified", "certified") else 1


if __name__ == "__main__":
    raise SystemExit(main())
