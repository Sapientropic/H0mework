#!/usr/bin/env python3
"""Run first-release mathematical consumers in verified public source views.

Runtime configuration uses h0mework/first-release-runtime@1. Each view selects
an export-map revision and original paths; each check selects an audited kind.
Fresh views, logs and results stay in a new task directory under .local.
"""
from __future__ import annotations

import argparse
import ast
from contextlib import ExitStack, contextmanager, redirect_stderr, redirect_stdout
from datetime import datetime, timezone
from decimal import localcontext
from fractions import Fraction
import gzip
import hashlib
import importlib.abc
import importlib.machinery
import importlib.util
import inspect
import io
import itertools
import json
import lzma
import math
import os
from pathlib import Path, PurePosixPath
import re
import runpy
import shutil
import subprocess
import sys
import sysconfig
import tempfile
import time
import uuid
from zipfile import ZipFile

import source_view


ROOT = Path(__file__).resolve().parents[1]
SCHEMA = "h0mework/first-release-runtime@1"
REPORT_SCHEMA = "h0mework/first-release-replay@1"
BELL = "Verification/physics/stage10/independent-bell"
ECD = "Verification/physics/low-energy-phenomenology/external-composite-decay"
KINDS = {"core-identities", "fock-current", "theory-blind", "exact-source-controls",
         "eth-bell", "munich-bell", "nist-witness-consumers", "nist-nominal-replay", "nist-public-member",
         "munich-contract", "quantum-independent"}
GAMMA_PROGRAMS = {
    ECD + "/check_clock_phi_native_matched_gamma_budget.py",
    ECD + "/check_clock_phi_renormalized_second_green_tail.py",
    ECD + "/check_clock_phi_matched_diffusion_source.py",
}
GAMMA_OUTPUTS = {
    ECD + "/check_clock_phi_native_matched_gamma_budget.py": ECD + "/clock-phi-native-matched-gamma-budget-check.json",
    ECD + "/check_clock_phi_renormalized_second_green_tail.py": ECD + "/clock-phi-renormalized-second-green-tail-check.json",
    ECD + "/check_clock_phi_matched_diffusion_source.py": ECD + "/clock-phi-matched-diffusion-source-check.json",
}
NIST_CONSUMERS = {
    "observable-closure/verify_slice.py": "run",
    "observable-closure/verify_receiver.py": "run",
    "observable-closure/full-statistical-fiber/verify_fiber.py": "verify",
    "public-review/source-compression/statistics_verify.py": "generate",
    "public-review/source-compression/domain_verify.py": "verify_witness",
    "public-review/source-compression/verify.py": "generate",
}
NIST_CONTROL_TESTS = {BELL + "/nist-real/nominal-replay/observable-closure/" + name
                      for name in ("tests.py", "slice_tests.py", "receiver_tests.py")}
NIST_CONTROL_TESTS |= {BELL + "/nist-real/nominal-replay/public-review/source-compression/" + name
                       for name in ("test_independent.py", "test_statistics_verify.py", "test_domain.py", "test_domain_verify.py")}
MUNICH_CONTRACTS = {
    "identification": ("identify_verify.py", "test_identification.py", "test_identification_independent.py", "test_identify_verify.py"),
    "shared-response": ("shared_response_verify.py", "test_shared_response.py", "test_shared_response_independent.py", "test_shared_response_verify.py"),
    "joint-response": ("joint_response_verify.py", "test_joint_response.py", "test_joint_response_independent.py", "test_joint_response_verify.py"),
    "atomic-forward": ("atomic_forward_verify.py", "test_atomic_forward.py", "test_atomic_forward_independent.py", "test_atomic_forward_verify.py"),
    "detector-fiber": ("detector_fiber_verify.py", "test_detector_fiber.py", "test_detector_fiber_independent.py", "test_detector_fiber_verify.py"),
    "pulse-realization": ("pulse_realization_verify.py", "test_pulse_realization.py", "test_pulse_realization_independent.py", "test_pulse_realization_verify.py"),
    "hardware-anchors": ("hardware_anchors_run.py", "test_hardware_anchors.py", "test_hardware_anchor_check.py", "test_hardware_anchors_run.py"),
}
ORIGINAL_CONTROL_TESTS = NIST_CONTROL_TESTS | {
    BELL + "/munich/readout-domain/" + name for entry in MUNICH_CONTRACTS.values() for name in entry[1:]}


class ReplayError(Exception):
    pass


def require(condition, reason):
    if not condition:
        raise ReplayError(reason)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def relative(value):
    try:
        return source_view.source_path(value)
    except source_view.ViewError as error:
        raise ReplayError(str(error)) from error


def inside(root, value):
    path = root / relative(value)
    require(path.resolve().is_relative_to(root.resolve()), "Path leaves its declared root")
    return path


def read_json(path):
    try:
        return json.loads(Path(path).read_bytes(), parse_constant=lambda _: (_ for _ in ()).throw(ValueError("Nonfinite JSON")))
    except (OSError, ValueError) as error:
        raise ReplayError(f"Cannot read JSON: {Path(path).name}") from error


def write_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8") as stream:
        json.dump(value, stream, ensure_ascii=False, indent=2, allow_nan=False)
        stream.write("\n")


def load_config(path):
    document = read_json(path)
    if isinstance(document, dict) and document.get("schema") != SCHEMA:
        document = document.get("runtime", document.get("checks", {}).get("runtime")
                                if isinstance(document.get("checks"), dict) else None)
    require(isinstance(document, dict) and document.get("schema") == SCHEMA,
            f"Runtime configuration must use {SCHEMA}")
    require(isinstance(document.get("views"), dict), "Runtime views must be an object")
    require(isinstance(document.get("checks"), list) and document["checks"],
            "Runtime checks must be a nonempty array")
    seen = set()
    for check in document["checks"]:
        require(isinstance(check, dict) and isinstance(check.get("id"), str) and
                re.fullmatch(r"[a-z0-9][a-z0-9_-]*", check["id"]),
                "Check id must contain lowercase letters, digits, hyphens or underscores")
        require(check["id"] not in seen, "Duplicate check id")
        seen.add(check["id"])
        require(isinstance(check.get("kind"), str) and check["kind"] in KINDS,
                f"Unsupported check kind: {check.get('kind')}")
        require(isinstance(check.get("tier"), str) and check["tier"] in {"entry", "bell", "full"}, "Unknown check tier")
        if check["kind"] not in {"core-identities", "quantum-independent"}:
            require(isinstance(check.get("view"), str) and check["view"] in document["views"],
                    "Check has no declared source view")
        if check["kind"] == "exact-source-controls":
            require(isinstance(check.get("program"), str) and check["program"] in GAMMA_OUTPUTS,
                    "Unknown exact source control program")
            expected = GAMMA_OUTPUTS[check["program"]]
            require(check.get("output", expected) == expected, "Declared output differs from the original program")
            check["output"] = expected
        if check["kind"] == "quantum-independent":
            check["quantum_config"] = relative(check.get("quantum_config", "checks/first-release-quantum.json"))
            ids = check.get("ids")
            require(ids is None or isinstance(ids, list) and ids and
                    all(isinstance(name, str) and re.fullmatch(r"[a-z0-9][a-z0-9-]*", name) for name in ids) and
                    len(set(ids)) == len(ids), "Quantum ids must be a nonempty array of unique ids")
        if "historical_views" in check:
            historical = check["historical_views"]
            require(check["kind"] == "nist-witness-consumers" and isinstance(historical, list) and
                    all(isinstance(name, str) and name in document["views"] for name in historical) and
                    len(set(historical)) == len(historical), "Historical source views must be explicit unique NIST view ids")
    return document


def select_checks(config, mode):
    tiers = {mode} if mode != "full" else {"entry", "bell", "full"}
    checks = [row for row in config["checks"] if row["tier"] in tiers]
    require(checks, f"No configured {mode} checks")
    required = config.get("required", {})
    require(isinstance(required, dict), "Required check tiers must be an object")
    requested = required.get(mode, [])
    require(isinstance(requested, list) and all(isinstance(name, str) for name in requested),
            "Required checks must be an array of ids")
    require(set(requested) <= {row["id"] for row in checks}, "Required check is absent from this tier")
    return checks


def python_executable(value):
    require(isinstance(value, str) and value, "Python executable is missing")
    if "/" in value or "\\" in value:
        executable = Path(value)
        if not executable.is_absolute():
            executable = ROOT / executable
        executable = executable.absolute()
        require(executable.is_file(), "Python executable is unavailable")
        # Preserve the virtualenv symlink: resolving it changes Python's venv.
        return str(executable)
    executable = shutil.which(value)
    require(executable is not None, "Python executable is unavailable")
    return executable


@contextmanager
def map_root(root, export_map=None):
    previous = source_view.ROOT, source_view.EXPORT_MAP
    source_view.ROOT, source_view.EXPORT_MAP = root, export_map or root / "tools/export-map.json"
    try:
        yield
    finally:
        source_view.ROOT, source_view.EXPORT_MAP = previous


def prepare_view(root, destination, configuration, omit=(), export_map=None):
    require(not destination.exists(), "A source view must be new")
    ref = configuration.get("ref")
    require(isinstance(ref, str) and ref, "A source view needs an explicit revision")
    paths = configuration.get("paths", [])
    prefixes = configuration.get("prefixes", [])
    require(isinstance(paths, list) and isinstance(prefixes, list), "View selectors must be arrays")
    require(paths or prefixes, "A runtime source view needs explicit nonempty selectors")
    with map_root(root, export_map):
        outputs, skipped = source_view.reconstruct(paths=paths, prefixes=prefixes, at=ref)
        require(not skipped, "Required source-view inputs were skipped")
        require(set(paths) <= set(outputs), "Explicit source input is absent at the pinned revision")
        data, modules, artifacts, _ = source_view.load_map()
        revision = data.get("revisions", {}).get(ref, ref)
        if revision == ref:
            known = {r["source_revision"] for rows in (*modules.values(), *artifacts.values()) for r in rows}
            hits = [value for value in known if value.startswith(ref)]
            require(len(hits) == 1, "Source revision is ambiguous")
            revision = hits[0]
        bindings = {}
        excluded = {relative(value) for value in omit}
        for name, raw in outputs.items():
            if name in excluded:
                continue
            candidates = modules.get(name, []) + artifacts.get(name, [])
            row = source_view.pick(candidates, name, None, revision)
            require(row is not None, "Missing mapped source identity")
            bindings[name] = {"view_sha256": sha(raw), "source_sha256": row["source_sha256"],
                              "source_revision": row["source_revision"],
                              "source_revisions": row.get("source_revisions", [row["source_revision"]]),
                              "publication": row.get("publication")}
        public_inputs = configuration.get("public_inputs", [])
        require(isinstance(public_inputs, list), "Explicit public source inputs must be an array")
        for row in public_inputs:
            require(isinstance(row, dict) and all(isinstance(row.get(key), str) for key in
                    ("path", "sha256", "original_path", "source_repository", "source_commit")),
                    "Public source input needs an explicit path, digest, original path and upstream identity")
            source, name = relative(row["path"]), relative(row["original_path"])
            require(not {".local", ".lake", ".git"}.intersection(PurePosixPath(source).parts),
                    "Public source input cannot use a runtime or Git cache")
            require(name not in outputs and name not in excluded, "Public source input conflicts with a mapped input or fresh output")
            require(re.fullmatch(r"[0-9a-f]{64}", row["sha256"]) and
                    re.fullmatch(r"[0-9a-f]{40}", row["source_commit"]) and
                    re.fullmatch(r"https://[A-Za-z0-9.-]+/[^\s?#@]+", row["source_repository"]),
                    "Public source input has an invalid upstream identity")
            raw = inside(root, source).read_bytes()
            require(sha(raw) == row["sha256"], "Explicit public source input changed: " + source)
            outputs[name] = raw
            bindings[name] = {"view_sha256": row["sha256"], "source_sha256": row["sha256"],
                              "source_revision": row["source_commit"], "source_revisions": [row["source_commit"]],
                              "source_repository": row["source_repository"], "publication": None,
                              "source_origin": "explicit-public-upstream-source", "public_input_path": source}
        destination.mkdir(parents=True)
        for name, identity in bindings.items():
            path = inside(destination, name)
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(outputs[name])
    return {"ref": ref, "source_revision": revision, "bindings": bindings,
            "omitted_fresh_outputs": sorted(excluded), "public_inputs": public_inputs}


class PublicInputs:
    def __init__(self, root, bindings, historical=()):
        self.root, self.bindings = root.resolve(), bindings
        self.historical = [PublicInputs(Path(view["root"]), view["bindings"]) for view in historical]

    def path(self, name):
        path = inside(self.root, name)
        require(name in self.bindings, f"Input is not in the verified source view: {name}")
        require(path.is_file() and sha(path.read_bytes()) == self.bindings[name]["view_sha256"],
                f"Source-view input changed: {name}")
        return path

    def verify_all(self):
        for name in self.bindings:
            self.path(name)
        for view in self.historical:
            view.verify_all()

    def load(self, path, name):
        location = self.path(path)
        sys.path.insert(0, str(location.parent))
        spec = importlib.util.spec_from_file_location(name, location)
        require(spec is not None and spec.loader is not None, "Cannot load original mathematical module")
        module = importlib.util.module_from_spec(spec)
        sys.modules[name] = module
        spec.loader.exec_module(module)
        return module


class RuntimeInputs:
    """Reject ambient input, network and process fallbacks inside one worker."""
    def __init__(self, roots, files=(), processes=()):
        self.roots = {Path(path).resolve() for path in roots}
        self.files = {Path(path).resolve() for path in files}
        self.processes = {tuple(command) for command in processes}
        self.temporary_root = Path(tempfile.gettempdir()).resolve()

    def audit(self, event, arguments):
        if event == "tempfile.mkdtemp":
            path = Path(arguments[0]).resolve()
            require(path.parent == self.temporary_root or any(path.is_relative_to(root) for root in self.roots),
                    "Original runtime requested a temporary directory outside its public inputs")
            self.roots.add(path)
        elif event == "open" and not isinstance(arguments[0], int):
            path = Path(os.fsdecode(arguments[0])).resolve()
            write = arguments[2] & (os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND)
            require(any(path.is_relative_to(root) for root in self.roots) or
                    (not write and path in self.files) or path == Path(os.devnull),
                    "Original runtime attempted file access outside its explicit public inputs: " + path.name)
        elif event == "subprocess.Popen":
            require(isinstance(arguments[1], (list, tuple)) and tuple(arguments[1]) in self.processes,
                    "Original runtime attempted an undeclared Git/build/program process")
        elif event in {"socket.connect", "socket.getaddrinfo"}:
            raise ReplayError("Original runtime attempted a network input fallback")


def worker_input_scope(spec, output, inputs):
    task = Path(spec["map_snapshot"]).parent
    libraries = [sysconfig.get_path(key) for key in ("stdlib", "platstdlib", "purelib", "platlib")]
    roots = [task, ROOT / "tools", *[path for path in libraries if path]]
    files = []
    if spec["check"].get("frozen"):
        files.append(inside(ROOT, spec["check"]["frozen"]))
    kind, commands = spec["check"]["kind"], []
    if kind == "core-identities":
        files.append(ROOT / "scripts/physics/common-source/check_core_identities.py")
        commands.append([spec["python"], str(output / "check_core_identities.py")])
    elif kind == "fock-current":
        commands.append([spec["python"], str(inputs.path(spec["check"]["program"])), "--output", str(output / "fock-current.json")])
    elif kind == "exact-source-controls":
        commands.append([spec["python"], str(inputs.path(spec["check"]["program"]))])
    elif kind == "quantum-independent":
        files.append(inside(ROOT, spec["check"]["quantum_config"]))
        commands.append(quantum_command(spec["check"], output, spec["python"]))
    if spec.get("archive_dir"):
        names = ([spec["check"].get("archive_name", "storz-2023-rawData.zip")] if kind == "eth-bell" else
                 ["Bell_2016-04-15.zip", "Bell_2016-06-14.zip"] if kind == "munich-bell" else [])
        files.extend(inside(Path(spec["archive_dir"]), name) for name in names)
    scope = RuntimeInputs(roots, files, commands)
    sys.addaudithook(scope.audit)
    return scope


def table(records, constructor):
    require(isinstance(records, list) and len(records) == 32, "Incomplete Born probability carrier")
    answer = {}
    for row in records:
        require(all(type(row.get(key)) is bool for key in ("herald", "outcome_a", "outcome_b")),
                "Nonliteral outcome label")
        require(all(type(row.get(key)) is int and row[key] in (0, 1) for key in ("setting_a", "setting_b")),
                "Nonliteral setting label")
        key = tuple(row[name] for name in ("herald", "setting_a", "setting_b", "outcome_a", "outcome_b"))
        require(key not in answer, "Duplicate Born record")
        value = row["probability"]
        require(set(value) == {"r", "s"} and all(str(Fraction(value[k])) == value[k] for k in value),
                "Born coefficient must be an exact canonical rational")
        answer[key] = constructor.Q2(Fraction(value["r"]), Fraction(value["s"]))
    require(set(answer) == set(itertools.product((False, True), (0, 1), (0, 1), (False, True), (False, True))),
            "Missing Born context")
    return answer


def blind_born(inputs, check, output):
    base = relative(check.get("root", BELL + "/theory-blind"))
    constructor = inputs.load(base + "/constructor.py", "constructor")
    independent = inputs.load(base + "/independent_born.py", "_h0_blind_independent")
    require(not inspect.signature(constructor.build_prediction).parameters, "Constructor is not nullary")
    primary, other = constructor.build_prediction(), independent.generate()
    raw, aligned = table(primary["records"], constructor), table(primary["aligned_records"], constructor)
    require(raw == table(other["raw_records"], constructor), "Full source Born contraction disagrees")
    require(aligned == table(other["aligned_records"], constructor), "Aligned Born contraction disagrees")
    require(other["dimension"] == 8 and other["checks"]["spectral_projection_count"] == 32,
            "Independent source carrier changed")
    for h, a, b in itertools.product((False, True), (0, 1), (0, 1)):
        require(sum(raw[h, a, b, x, y] for x, y in itertools.product((False, True), repeat=2)) == constructor.lift(1),
                "Born distribution is not normalized")
        for bit in (False, True):
            require(sum(raw[h, a, b, bit, y] for y in (False, True)) == constructor.lift(Fraction(1, 2)),
                    "Alice marginal changed")
            require(sum(raw[h, a, b, x, bit] for x in (False, True)) == constructor.lift(Fraction(1, 2)),
                    "Bob marginal changed")
        for x, y in itertools.product((False, True), repeat=2):
            probability = raw[h, a, b, x, y]
            require(probability.sign() >= 0 and (constructor.lift(1) - probability).sign() >= 0,
                    "Probability is outside its physical domain")
            require(aligned[h, a, b, x ^ (h and a == 1), y] == probability,
                    "Herald correction does not commute")
    for h in (False, True):
        correlations = [sum(constructor.sign(x) * constructor.sign(y) * raw[h, a, b, x, y]
                            for x, y in itertools.product((False, True), repeat=2))
                        for a, b in itertools.product((0, 1), repeat=2)]
        score = -correlations[0] - correlations[1] - constructor.sign(h) * correlations[2] + constructor.sign(h) * correlations[3]
        require(score == constructor.Q2(Fraction(0), Fraction(2)) and (score - 2).sign() > 0,
                "Source CHSH value changed")
    require(len(other["finite_unit_phase_controls"]) == 4 and all(
        row["full_32_probabilities_equal_point_zero"] is True for row in other["finite_unit_phase_controls"]),
        "Independent phase controls are incomplete")
    write_json(output / "primary.json", primary)
    write_json(output / "independent.json", other)
    return {"raw_probability_records": 32, "aligned_probability_records": 32,
            "dimension": 8, "normalized_distributions": 8, "phase_controls": 4,
            "empirical_inputs": 0}


def archive(directory, name, expected):
    require(directory is not None, "This check requires explicit --archive-dir")
    require(PurePosixPath(relative(name)).name == name, "Archive name must be a single filename")
    path = inside(directory, name)
    require(path.is_file(), f"Missing explicitly declared archive: {name}")
    raw = path.read_bytes()
    require(len(raw) == expected["bytes"] and sha(raw) == expected["sha256"], "Official archive bytes changed")
    return path, {"name": name, "bytes": len(raw), "sha256": sha(raw)}


def eth_bell(inputs, check, output, archive_dir):
    base = relative(check.get("root", BELL))
    metadata = read_json(inputs.path(base + "/custody/r0002-storz2023-metadata.json"))
    name = check.get("archive_name", "storz-2023-rawData.zip")
    path, binding = archive(archive_dir, name, metadata["archive"])
    member = next(row for row in metadata["archive"]["members"] if row["role"] == "evaluation_event_stream")
    with ZipFile(path) as zipped:
        require(member["member"] in zipped.namelist(), "Original event member is missing")
        raw = zipped.read(member["member"])
        require(len(raw) == member["bytes"] and sha(raw) == member["sha256"], "Original ordered events changed")
    reader = inputs.load(base + "/reader.py", "_h0_eth_reader")
    analysis = inputs.load(base + "/analyze.py", "_h0_eth_analysis")
    recompute = inputs.load(base + "/evidence/recompute.py", "_h0_eth_decimal")
    instrument = read_json(inputs.path(base + "/instrument.json"))
    primary = analysis.analyze(reader.trials(path), instrument)
    with localcontext() as context:
        context.prec = 80
        recompute.self_check()
        independent = recompute.replay(path)
        comparison = recompute.compare(independent, read_json(inputs.path(base + "/lock.json")))
    require(primary["trial_cap"] == independent["n_trials"] == 100000, "Incomplete ETH trial stream")
    require(independent["prefixes_evaluated_per_radius"] == 100001 and len(independent["radii"]) == 6,
            "Incomplete ETH all-prefix/radius coverage")
    old = read_json(inputs.path(base + "/evidence/results.json"))
    require(primary["models"][0]["context_counts"] == old["models"][0]["context_counts"],
            "ETH complete outcome counts disagree")
    write_json(output / "primary.json", primary)
    write_json(output / "independent80.json", independent)
    write_json(output / "comparison.json", comparison)
    return {"archive": binding, "trials": 100000, "prefixes_per_radius": 100001,
            "radii": 6, "decimal_precision": 80, "comparison": comparison,
            "scope": "Original ideal joint-model statistic; original instrument-bridge failure retained"}


def munich_bell(inputs, check, output, archive_dir):
    base = relative(check.get("root", BELL + "/munich"))
    schema = inputs.load(base + "/schema.py", "_h0_munich_schema")
    parser = inputs.load(base + "/invariant_independent.py", "_h0_munich_parser")
    independent = inputs.load(base + "/readout-domain/independent.py", "_h0_munich_born")
    points = independent.load_witness(inputs.path(base + "/readout-domain/primitive-witness-c0002.json").read_bytes())
    old_firsts = [independent.strict_json(inputs.path(base + "/" + name).read_bytes())
                  for name in independent.OLD_FIRSTS]
    reports, bindings, parsed, independently_parsed = [], [], {}, {}
    for spec, other_spec in zip(schema.ARCHIVES, parser.ARCHIVE_IDENTITIES, strict=True):
        path, bound = archive(archive_dir, spec.name, {"bytes": spec.bytes, "sha256": spec.sha256})
        primary_run = schema.admit_archive(archive_dir, spec)
        other_run = parser.archive_run(path.read_bytes(), other_spec)
        original_bits = lambda run: [(r.row, r.h, r.a, r.b, r.x, r.y, r.row_a, r.row_b) for r in run.trials]
        require(original_bits(primary_run) == original_bits(other_run), "Independent complete pair parsers disagree")
        require(primary_run.audit == other_run.audit and primary_run.token_dictionaries == other_run.token_dictionaries,
                "Independent full local-row admission disagrees")
        legacy_cross = independent.legacy_cross(other_run, old_firsts)
        report = independent.certify_run(other_run, points[spec.run])
        require(report["all_pair_records_scored"] is True and report["all_prefixes_below_threshold_certified"] is True,
                "Original complete point does not pass every prefix")
        require(report["prefixes_checked"] == len(primary_run.trials) and report["threshold"] == "40",
                "Original all-prefix threshold or scope changed")
        report["legacy_cross"] = legacy_cross
        reports.append(report)
        bindings.append(bound)
        parsed[spec.run] = primary_run
        independently_parsed[spec.run] = other_run
    require(sum(row["trials"] for row in reports) == 20403, "Incomplete original two-run selection")
    first = read_json(inputs.path(base + "/readout-domain/independent-first-c0002.json"))
    originals = {row["run"]: row for row in first["runs"]}
    for row in reports:
        for key in ("factor_sequence_sha256", "trial_bit_sequence_sha256", "four_outcomes", "pooled_counts"):
            require(row[key] == originals[row["run"]][key], f"Original complete prefix identity changed: {key}")
    history = inputs.load(base + "/readout-domain/history_feed.py", "history_feed")
    history_independent = inputs.load(base + "/readout-domain/history_feed_independent.py", "history_feed_independent")
    clock = inputs.load(base + "/readout-domain/clock_observation.py", "_h0_record_clock")
    clock_independent = inputs.load(base + "/readout-domain/clock_observation_independent.py", "_h0_record_clock_independent")
    paid = read_json(inputs.path(base + "/primary-first-mu0001.1.json"))
    histories = history.load_histories(archive_dir, paid)
    summaries = [row.summary() for row in histories]
    cross = list(history_independent.load_summaries(archive_dir, paid))
    require(summaries == cross, "Independent complete record observers disagree")
    require(sum(row["records"] for row in summaries) == 41673 and
            sum(row["unpaired_records"] for row in summaries) == 867, "Original full records were dropped")
    local_clocks = []
    for record in histories:
        primary_clock = clock.summarize(record)
        # Independent observations are raw nine-field tuples, not the primary dataclass.
        raw_records = record.observations
        other_clock = clock_independent.summarize(record.run, record.role, raw_records, record.paired_rows)
        require(primary_clock == other_clock, "Independent complete successor-clock observers disagree")
        local_clocks.append(primary_clock)
    old_history = read_json(inputs.path(base + "/readout-domain/history-first-hr0001.1.json"))
    require(summaries == old_history["primary"], "Original complete history fields changed")
    old_clock = read_json(inputs.path(base + "/readout-domain/clock-first-cl0001.json"))
    require(local_clocks == old_clock["local_clock_tables"], "Original successor-clock tables changed")
    pair_clocks = []
    for run in schema.RUNS:
        first_history, second_history = [row for row in histories if row.run == run]
        primary_clock = clock.pair_summary(first_history, second_history, parsed[run])
        other_clock = clock_independent.pair_summary(
            run, first_history.observations, second_history.observations,
            first_history.paired_rows, second_history.paired_rows, independently_parsed[run])
        require(primary_clock == other_clock, "Independent complete pair-clock observers disagree")
        pair_clocks.append(primary_clock)
    require(pair_clocks == old_clock["pair_clock_tables"], "Original complete pair-clock cells changed")
    write_json(output / "prefixes.json", {"runs": reports})
    write_json(output / "history.json", {"primary": summaries, "independent": cross})
    write_json(output / "local-clocks.json", {"tables": local_clocks})
    write_json(output / "pair-clocks.json", {"tables": pair_clocks})
    return {"archives": bindings, "trials": 20403, "all_prefixes_checked": True,
            "public_local_records": 41673, "unpaired_records": 867,
            "source_clock_record_square_certified": False,
            "pair_clock_joint_distribution_preserved": False,
            "scope": "Original complete point, local records and local successor clocks"}


def exact_controls(result, frozen):
    require(result.get("all_pass") is True, "Exact source arithmetic failed")
    require(isinstance(result.get("checks"), dict) and result["checks"] and all(v is True for v in result["checks"].values()),
            "Exact source checks are absent or failed")
    negative = result.get("effective_negative_controls")
    require(isinstance(negative, dict) and negative and all(v is True for v in negative.values()),
            "Effective negative controls are absent or failed")
    require(result == frozen, "Exact source controls differ from their frozen scientific receipt")


def close_numbers(actual, original, tolerance):
    if type(original) is float:
        require(type(actual) in (float, int) and math.isfinite(actual) and abs(actual - original) <= tolerance,
                "Numerical readout differs beyond its original tolerance")
    elif isinstance(original, dict):
        require(isinstance(actual, dict) and actual.keys() == original.keys(), "Scientific readout fields changed")
        for key in original:
            close_numbers(actual[key], original[key], tolerance)
    elif isinstance(original, list):
        require(isinstance(actual, list) and len(actual) == len(original), "Scientific readout inventory changed")
        for value, expected in zip(actual, original, strict=True):
            close_numbers(value, expected, tolerance)
    else:
        require(type(actual) is type(original) and actual == original, "Exact scientific readout changed")


def validate_fock(result, frozen):
    require(result.get("status") == "PASS" and result.get("modes") == 8 and result.get("Fock_dimension") == 256,
            "Full Fock carrier or result changed")
    require(result["particle_sector_dimensions"] == frozen["particle_sector_dimensions"] and
            result["random_seed"] == frozen["random_seed"] and result["tolerance"] == frozen["tolerance"],
            "Original Fock conventions or numerical inputs changed")
    require(math.isfinite(result["maximum_absolute_residual"]) and
            0 <= result["maximum_absolute_residual"] <= frozen["tolerance"], "Full Fock residual exceeds original tolerance")
    require(result["checks"].keys() == frozen["checks"].keys(), "Fock check families changed")
    for name, row in result["checks"].items():
        old = frozen["checks"][name]
        for key in old:
            if key not in {"maximum_absolute_residual", "maximum_residual", "max_residual", "residual"}:
                require(row[key] == old[key], f"Fock consumer coverage changed: {name}.{key}")
            else:
                require(math.isfinite(row[key]) and 0 <= row[key] <= frozen["tolerance"], "A Fock family residual failed")
    for key in ("source_parameters", "conventions", "source_points", "changed_observable_negative_control",
                "arbitrary_complex_matrix_trials", "scope"):
        close_numbers(result[key], frozen[key], frozen["tolerance"])


def run_program(inputs, check, output, executable):
    kind = check["kind"]
    frozen_path = inside(ROOT, check["frozen"])
    frozen_sha = sha(frozen_path.read_bytes())
    require(check.get("frozen_sha256", frozen_sha) == frozen_sha, "Frozen comparison receipt changed before execution")
    if kind == "core-identities":
        original = ROOT / "scripts/physics/common-source/check_core_identities.py"
        require(original.is_file(), "Finite core checker is missing")
        frozen_identity = read_json(inside(ROOT, check["frozen"]))
        require(sha(original.read_bytes()) == frozen_identity["generator_sha256"], "Finite core source changed")
        program = output / original.name
        program.write_bytes(original.read_bytes())
        destination = output / "core-identity-checks.json"
        command = [executable, str(program)]
        completed = subprocess.run(command, cwd=output, capture_output=True, text=True, check=False)
    else:
        name = relative(check["program"])
        if kind == "fock-current":
            require(name == "Verification/physics/quantization-current/check.py", "Unexpected Fock program")
            destination = output / "fock-current.json"
            command = [executable, str(inputs.path(name)), "--output", str(destination)]
        else:
            require(name in GAMMA_PROGRAMS, "Exact source program is outside the audited group")
            require(check["output"] == GAMMA_OUTPUTS[name], "Declared output differs from the original program")
            destination = inside(inputs.root, check["output"])
            require(not destination.exists(), "Fresh output would overwrite a frozen source-view receipt")
            command = [executable, str(inputs.path(name))]
        completed = subprocess.run(command, cwd=output, capture_output=True, text=True, check=False)
    (output / "program.stdout.log").write_text(completed.stdout)
    (output / "program.stderr.log").write_text(completed.stderr)
    require(completed.returncode == 0, f"Original program exited {completed.returncode}")
    require(destination.is_file(), "Original program produced no fresh receipt")
    require(sha(frozen_path.read_bytes()) == frozen_sha, "Frozen comparison receipt changed during execution")
    result, frozen = read_json(destination), read_json(frozen_path)
    if kind == "core-identities":
        require(result["status"] == "passed" and result["families"] == frozen["families"] and
                result["evaluations"] == frozen["evaluations"] and
                math.isfinite(result["max_residual"]) and result["max_residual"] <= frozen["absolute_tolerance"],
                "Finite core identities do not meet original coverage/tolerance")
    elif kind == "fock-current":
        validate_fock(result, frozen)
    else:
        exact_controls(result, frozen)
    return {"program_exit_code": completed.returncode, "fresh_output": str(destination.relative_to(inputs.root))
            if inputs is not None and destination.is_relative_to(inputs.root) else destination.name,
            "fresh_sha256": sha(destination.read_bytes()), "frozen_sha256": frozen_sha}


class RecordedSourceBindings:
    """Resolve recorded source labels using verified published input bytes.

    Old Git commits remain historical receipt labels. This provider proves the
    available source/payload identity and never invents a Git ancestry result.
    """
    def __init__(self, inputs, preferences=None, fresh_root=None):
        self.inputs = inputs
        self.preferences = preferences or {}
        self.fresh_root = None if fresh_root is None else fresh_root.resolve()
        self.records = {}
        self.raw_identities = {}
        self.logical_hashes = set()
        self.used = {}
        self.adaptations = {}
        for name, row in inputs.bindings.items():
            self.raw_identities.setdefault(row["view_sha256"], set()).add(row["source_sha256"])
            if name.endswith(".json"):
                self.collect(read_json(inputs.path(name)))

    def collect(self, value):
        if isinstance(value, dict):
            for key in ("logical_sha256", "logical_json_sha256"):
                if isinstance(value.get(key), str) and re.fullmatch(r"[0-9a-f]{64}", value[key]):
                    self.logical_hashes.add(value[key])
            path, digest, commit = value.get("path"), value.get("sha256"), value.get("commit")
            if isinstance(path, str) and isinstance(digest, str) and isinstance(commit, str):
                if path in self.inputs.bindings and digest == self.inputs.bindings[path]["source_sha256"]:
                    self.records.setdefault(path, set()).add((commit, digest))
            freeze = value.get("freeze_commit")
            if isinstance(freeze, str) and isinstance(value.get("source_bindings"), list):
                for row in value["source_bindings"]:
                    if isinstance(row, dict):
                        name, digest = row.get("path"), row.get("sha256")
                        if isinstance(name, str) and name in self.inputs.bindings and digest == self.inputs.bindings[name]["source_sha256"]:
                            self.records.setdefault(name, set()).add((freeze, digest))
            for key, item in value.items():
                if key in self.inputs.bindings and isinstance(item, dict):
                    commit, digest = item.get("commit"), item.get("sha256")
                    if isinstance(commit, str) and digest == self.inputs.bindings[key]["source_sha256"]:
                        self.records.setdefault(key, set()).add((commit, digest))
                self.collect(item)
        elif isinstance(value, list):
            for item in value:
                self.collect(item)

    def decoder(self, name, function):
        def decode(raw, *args, **kwargs):
            decoded = function(raw, *args, **kwargs)
            stored = sha(raw)
            if stored in self.raw_identities:
                logical = sha(decoded)
                self.logical_hashes.add(logical)
                self.adaptations[(stored, name)] = {
                    "decoder": name, "stored_view_sha256": stored,
                    "stored_source_sha256": sorted(self.raw_identities[stored]),
                    "logical_sha256": logical, "decoded_bytes_modified": False}
            return decoded
        return decode

    def name(self, path):
        path = Path(path).resolve()
        require(path.is_relative_to(self.inputs.root), "Legacy source reference leaves its public view")
        name = path.relative_to(self.inputs.root).as_posix()
        self.inputs.path(name)
        return name

    def digest(self, value):
        if isinstance(value, (bytes, bytearray)):
            actual = sha(value)
            originals = self.raw_identities.get(actual)
            if originals is None:
                return actual
            require(len(originals) == 1, "Published payload has ambiguous original identities; use an explicit source path")
            return next(iter(originals))
        path = Path(value).resolve()
        if self.fresh_root is not None and path.is_relative_to(self.fresh_root):
            require(path.is_file(), "Fresh mathematical receipt is missing")
            return sha(path.read_bytes())
        name = self.name(path)
        return self.inputs.bindings[name]["source_sha256"]

    def commit_identity(self, name, commit):
        row = self.inputs.bindings[name]
        labels = {label for label, digest in self.records.get(name, set())
                  if digest == row["source_sha256"]} | set(row["source_revisions"])
        if re.fullmatch(r"[0-9a-f]{7,39}", commit):
            matches = {label for label in labels if re.fullmatch(r"[0-9a-f]{40}", label) and label.startswith(commit)}
            require(len(matches) <= 1, "Recorded short source label has multiple registered full identities: " + name)
            if matches:
                return next(iter(matches))
        return commit

    def binding(self, path, commit=None):
        name = self.name(path)
        row = self.inputs.bindings[name]
        recorded = self.records.get(name, set())
        chosen = commit or self.preferences.get(name)
        if chosen is None:
            candidates = {self.commit_identity(name, old) for old, digest in recorded if digest == row["source_sha256"]}
            require(len(candidates) <= 1, f"Recorded source epoch is ambiguous: {name}")
            # A fresh verifier may freeze a mapped file that old receipts did
            # not label. Its source identity comes from the verified export.
            chosen = candidates.pop() if candidates else row["source_revision"]
        registered = {old for old, digest in recorded if digest == row["source_sha256"]} | set(row["source_revisions"])
        identity = self.commit_identity(name, chosen)
        require(identity in {self.commit_identity(name, label) for label in registered},
                f"Historical source label is unregistered: {name}")
        result = {"path": name, "commit": chosen, "sha256": row["source_sha256"]}
        self.used[(name, chosen)] = {**result, "view_sha256": row["view_sha256"],
                                   "export_source_revision": row["source_revision"],
                                   "binding_origin": "historical-receipt" if recorded else "verified-export-map",
                                   "Git_ancestry_replayed": False}
        return result

    def check_binding(self, row):
        require(isinstance(row, dict) and all(isinstance(row.get(k), str) for k in ("path", "sha256", "commit")),
                "Historical binding must contain path, digest and commit")
        name = relative(row["path"])
        require(name in self.inputs.bindings and row["sha256"] == self.inputs.bindings[name]["source_sha256"],
                f"Historical source digest differs: {name}")
        # This record came from a byte/payload-verified original receipt. Keep
        # its commit label, checking the current bytes rather than private Git.
        registered = {label for label, digest in self.records.get(name, set()) if digest == row["sha256"]}
        registered.update(self.inputs.bindings[name]["source_revisions"])
        require(self.commit_identity(name, row["commit"]) in {self.commit_identity(name, label) for label in registered},
                f"Historical source label was not read from a verified receipt: {name}")
        self.binding(self.inputs.path(name), row["commit"])

    def historical_bytes(self, row):
        require(isinstance(row, dict) and all(isinstance(row.get(key), str) for key in ("path", "commit", "sha256")),
                "Historical source must contain path, digest and commit")
        name, candidates = relative(row["path"]), []
        for view in [self.inputs, *self.inputs.historical]:
            identity = view.bindings.get(name)
            if identity is None or identity["source_sha256"] != row["sha256"]:
                continue
            labels = identity["source_revisions"]
            if row["commit"] not in labels and not (re.fullmatch(r"[0-9a-f]{7,39}", row["commit"]) and
                    len({label for label in labels if label.startswith(row["commit"])}) == 1):
                continue
            data = view.path(name).read_bytes()
            require(sha(data) == row["sha256"], "Historical source view does not preserve original bytes: " + name)
            candidates.append(data)
            self.used[(name, row["commit"])] = {
                **row, "view_sha256": identity["view_sha256"], "export_source_revision": identity["source_revision"],
                "binding_origin": "verified-historical-source-view", "Git_ancestry_replayed": False}
        require(candidates and len(set(candidates)) == 1, "Historical source has no unambiguous verified byte supplier: " + name)
        return candidates[0]

    def patch_module(self, module):
        location = getattr(module, "__file__", None)
        if not location or not Path(location).resolve().is_relative_to(self.inputs.root):
            return
        relative_name = self.name(location)
        if not (relative_name.startswith(BELL + "/nist-real/nominal-replay/") or
                relative_name == BELL + "/nist-real/nominal_optimum.py"):
            return
        legacy_root = getattr(module, "ROOT", None)
        if isinstance(legacy_root, Path) and legacy_root.resolve() != self.inputs.root:
            module.ROOT = self.inputs.root
            self.adaptations[(relative_name, "ROOT")] = {
                "path": relative_name, "binding": "ROOT", "identity": "verified public source-view root",
                "Git_ancestry_replayed": False}
            if getattr(module, "PROJECT", None) == legacy_root / "Lean":
                module.PROJECT = self.inputs.root / "Lean"
                self.adaptations[(relative_name, "PROJECT")] = {
                    "path": relative_name, "binding": "PROJECT", "identity": "verified public source-view Lean inputs",
                    "Git_ancestry_replayed": False}
        for name in ("sha", "sha256_file", "digest"):
            if callable(getattr(module, name, None)):
                setattr(module, name, self.digest)
        if callable(getattr(module, "frozen", None)):
            module.frozen = self.binding
        # The original binding_check functions contain only source-path/hash
        # and old Git guards; numerical/tree functions are never replaced.
        if relative_name.endswith("/statistics_verify.py"):
            module.binding_check = self.check_binding
        if relative_name in (BELL + "/nist-real/nominal-replay/replay.py",
                             BELL + "/nist-real/nominal-replay/independent_replay.py"):
            module.criterion_freeze = lambda: self.binding(Path(module.CRITERION_PATH))
        if relative_name == BELL + "/nist-real/nominal-replay/replay.py":
            module.find_repo_root = lambda _: str(self.inputs.root)
        if relative_name == BELL + "/nist-real/nominal-replay/observable-closure/primary.py":
            self.configuration_identity(module, relative_name)
        if relative_name == BELL + "/nist-real/nominal-replay/public-review/contrast-source/certify.py":
            self.contrast_kernel_identity(module, relative_name)
        if relative_name == BELL + "/nist-real/nominal-replay/public-review/multi-window/source_verify.py":
            self.source_audit_identity(module, relative_name)
        if relative_name == BELL + "/nist-real/nominal-replay/observable-closure/full-statistical-fiber/covariance_source_certify.py":
            self.covariance_kernel_identity(module, relative_name)

    def source_audit_identity(self, module, name):
        if getattr(module.certificate_bindings, "_h0_source_audit_identity", False):
            return
        source = ast.parse(self.inputs.path(name).read_text())
        functions = [node for node in source.body if isinstance(node, ast.FunctionDef) and node.name == "certificate_bindings"]
        require(len(functions) == 1 and not functions[0].decorator_list, "Original source audit intake is missing or changed")
        function = functions[0]
        original_sha = sha(ast.dump(function).encode())
        expected = ast.parse('blob = subprocess.check_output(["git", "show", original["commit"] + ":" + original["path"]], cwd=ROOT)').body[0]
        matches = [index for index, node in enumerate(function.body) if ast.dump(node) == ast.dump(expected)]
        require(len(matches) == 1, "Original source audit historical byte guard changed")
        helper = "_h0_verified_historical_source_bytes"
        require(helper not in module.__dict__, "Historical source helper collides with original source")
        module.__dict__[helper] = self.historical_bytes
        index = matches[0]
        function.body[index] = ast.copy_location(ast.parse("blob = " + helper + "(original)").body[0], function.body[index])
        rewritten = ast.fix_missing_locations(ast.Module(body=[function], type_ignores=[]))
        exec(compile(rewritten, str(self.inputs.path(name)), "exec"), module.__dict__)
        module.certificate_bindings._h0_source_audit_identity = True
        self.adaptations[(name, "certificate_bindings")] = {
            "path": name, "function": "certificate_bindings", "original_function_ast_sha256": original_sha,
            "public_function_ast_sha256": sha(ast.dump(function).encode()),
            "identity": "verified original historical source bytes; original mathematical AST equality and mutation control executed",
            "Git_ancestry_replayed": False}

    def covariance_kernel_identity(self, module, name):
        if getattr(module.consume, "_h0_covariance_kernel_identity", False):
            return
        source = ast.parse(self.inputs.path(name).read_text())
        functions = [node for node in source.body if isinstance(node, ast.FunctionDef) and node.name == "consume"]
        require(len(functions) == 1 and not functions[0].decorator_list, "Original covariance intake is missing or changed")
        function = functions[0]
        original_sha = sha(ast.dump(function).encode())
        # Freeze the reviewed function shape before replacing its two provenance
        # spans. All schema, scope, inventory, focused-kernel and Std3 guards stay.
        require(original_sha == "69d6a639bdd84de880d37f4236045b878d6f5d4cdc7c1e809889ff3bdc09d93d",
                "Original covariance provenance function changed")
        source_guard, history_guard = "_h0_verified_covariance_sources", "_h0_recorded_covariance_history"
        require(source_guard not in module.__dict__ and history_guard not in module.__dict__,
                "Covariance identity helpers collide with original source")

        def verified_sources(cert):
            reader = self.name(module.__file__)
            reader_identity = None
            for path, row in cert["bindings"].items():
                if path == "Lean/lakefile.toml":
                    continue
                binding = {**row, "path": path}
                if path == reader:
                    self.historical_bytes(binding)
                    reader_identity = {"historical_generation_driver": row,
                                       "current_consumer": self.binding(self.inputs.path(path))}
                else:
                    self.check_binding(binding)
            for row in read_json(self.inputs.path(self.name(module.HERE / "sources-source-realization.json")))["inputs"]:
                expected = (cert["bindings"]["Lean/lakefile.toml"]["sha256"] if row["path"] == "Lean/lakefile.toml"
                            else self.digest(self.inputs.path(row["path"])))
                require(expected == row["sha256"], "Covariance context source binding changed: " + row["path"])
            require(reader_identity is not None, "Original covariance reader identity is missing")
            return reader_identity

        def recorded_history(cert):
            record = {"historical_lakefile_binding": cert["bindings"]["Lean/lakefile.toml"],
                      "historical_import_closure": cert["actual_import_closure"],
                      "historical_dependency_closure_replayed": False, "historical_lake_registry_replayed": False,
                      "current_environment_fresh_kernel_check_claimed": False,
                      "kernel_gate": "separate public Lean package acceptance"}
            self.adaptations[(name, "consume")].update(record)
            self.adaptations[(name, "consume")]["owned_inputs_verified"] = len(cert["bindings"]) - 1
            return record

        module.__dict__[source_guard], module.__dict__[history_guard] = verified_sources, recorded_history
        source_statement = ast.copy_location(ast.parse("reader_identity = " + source_guard + "(cert)").body[0], function.body[13])
        history_statement = ast.copy_location(ast.parse("registry = " + history_guard + "(cert)").body[0], function.body[22])
        function.body = [*function.body[:13], source_statement, *function.body[18:22], history_statement, *function.body[33:]]
        rewritten = ast.fix_missing_locations(ast.Module(body=[function], type_ignores=[]))
        exec(compile(rewritten, str(self.inputs.path(name)), "exec"), module.__dict__)
        module.consume._h0_covariance_kernel_identity = True
        self.adaptations[(name, "consume")] = {
            "path": name, "function": "consume", "original_function_ast_sha256": original_sha,
            "public_function_ast_sha256": sha(ast.dump(function).encode()),
            "identity": "verified owned source bytes and original frozen covariance kernel scope/Std3 certificate",
            "Git_ancestry_replayed": False, "kernel_gate": "separate public Lean package acceptance"}

    def contrast_kernel_identity(self, module, name):
        if getattr(module.fastconsume, "_h0_contrast_kernel_identity", False):
            return
        source = ast.parse(self.inputs.path(name).read_text())
        functions = [node for node in source.body if isinstance(node, ast.FunctionDef) and node.name == "fastconsume"]
        require(len(functions) == 1 and not functions[0].decorator_list, "Original CT intake is missing or changed")
        function = functions[0]
        original_sha = sha(ast.dump(function).encode())
        source_guard = "_h0_verified_contrast_sources"
        history_guard = "_h0_recorded_contrast_history"
        require(source_guard not in module.__dict__ and history_guard not in module.__dict__,
                "CT identity helpers collide with original source")
        source_statements = ast.parse("""
for name, row in cert['bindings'].items():
    blob = subprocess.check_output(['git','show',row['commit']+':'+name],cwd=ROOT)
    require(hashlib.sha256(blob).hexdigest()==row['sha256'] and blob==(ROOT/name).read_bytes(),
            'CT source binding changed: '+name)
lake = cert['historical_lake_binding']
historical = subprocess.check_output(['git','show',lake['commit']+':Lean/lakefile.toml'],cwd=ROOT)
require(hashlib.sha256(historical).hexdigest()==lake['sha256'],'CT historical Lake configuration changed')
for row in json.loads((HERE/'sources.json').read_text())['inputs']:
    actual = hashlib.sha256(historical).hexdigest() if row['path']=='Lean/lakefile.toml' else digest(ROOT/row['path'])
    require(actual==row['sha256'],'CT contract context input changed: '+row['path'])
""").body
        history_statements = ast.parse("""
closure = cert['actual_import_closure']
current = source_closure(closure['toolchain_source_root'],True)
modules, search = current.pop('inventory'),current.pop('search_roots')
require(current==closure,'CT complete semantic import source changed')
registry = independent_registry_change(historical,(PROJECT/'lakefile.toml').read_bytes(),set(modules),search)
""").body
        for expected, replacement in ((source_statements, source_guard + "(cert)"),
                                      (history_statements, "registry = " + history_guard + "(cert, identity)")):
            count = len(expected)
            matches = [index for index in range(len(function.body) - count + 1)
                       if [ast.dump(node) for node in function.body[index:index + count]] ==
                       [ast.dump(node) for node in expected]]
            require(len(matches) == 1, "Original CT provenance statements changed")
            index = matches[0]
            function.body[index:index + count] = [ast.copy_location(ast.parse(replacement).body[0],
                                                                  function.body[index])]

        def verified_sources(cert):
            for path, row in cert["bindings"].items():
                require(row.get("path", path) == path, "CT source binding path changed")
                self.check_binding({**row, "path": path})
            for row in read_json(self.inputs.path(self.name(module.HERE / "sources.json")))["inputs"]:
                if row["path"] == "Lean/lakefile.toml":
                    require(row["sha256"] == cert["historical_lake_binding"]["sha256"],
                            "CT recorded historical Lake identity changed")
                else:
                    require(self.digest(self.inputs.path(row["path"])) == row["sha256"],
                            "CT contract context input changed: " + row["path"])

        def recorded_history(cert, identity):
            path = module.HERE.parent / "source-compression/kernel-certification-first.json"
            history = read_json(self.inputs.path(self.name(path)))["reused_CT_certificate"]
            # The registry and dependency closure describe the paid historical
            # kernel execution. Its current counterpart is the public Lean gate.
            expected = module.evidence_row(False)
            expected.update(module.CLAIMS)
            expected.update(evidence_valid=True, certificate_sha256=identity["sha256"],
                            certificate_commit=identity["commit"], authorized_axioms=cert["authorized_axioms"],
                            public_mouths=cert["public_mouths"], lake_registry=history["lake_registry"],
                            new_source_or_solver_execution=False)
            require(history == expected, "CT original frozen kernel intake changed")
            self.adaptations[(name, "fastconsume")].update({
                "owned_inputs_verified": len(cert["bindings"]),
                "historical_lake_binding": cert["historical_lake_binding"],
                "historical_import_closure": cert["actual_import_closure"],
                "retained_historical_lake_registry": history["lake_registry"]})
            return history["lake_registry"]

        module.__dict__[source_guard], module.__dict__[history_guard] = verified_sources, recorded_history
        rewritten = ast.fix_missing_locations(ast.Module(body=[function], type_ignores=[]))
        exec(compile(rewritten, str(self.inputs.path(name)), "exec"), module.__dict__)
        module.fastconsume._h0_contrast_kernel_identity = True
        self.adaptations[(name, "fastconsume")] = {
            "path": name, "function": "fastconsume", "original_function_ast_sha256": original_sha,
            "public_function_ast_sha256": sha(ast.dump(function).encode()),
            "identity": "verified owned source bytes and original frozen kernel scope/Std3 certificate",
            "Git_ancestry_replayed": False, "historical_dependency_closure_replayed": False,
            "historical_lake_registry_replayed": False, "kernel_gate": "separate public Lean package acceptance"}

    def configuration_identity(self, module, name):
        if getattr(module.configuration, "_h0_configuration_identity", False):
            return
        source = ast.parse(self.inputs.path(name).read_text())
        functions = [node for node in source.body if isinstance(node, ast.FunctionDef) and node.name == "configuration"]
        require(len(functions) == 1, "Original source configuration is missing or duplicated")
        function = functions[0]
        expected = ast.parse('subprocess.run(["git", "merge-base", "--is-ancestor", freeze["commit"], executable["commit"]], cwd=ROOT, check=True)').body[0]
        guards = [index for index, node in enumerate(function.body)
                  if ast.dump(node) == ast.dump(expected)]
        require(len(guards) == 1 and not function.decorator_list, "Original configuration ancestry guard changed")
        original_sha = sha(ast.dump(function).encode())
        helper = "_h0_verified_configuration_source_identity"
        require(helper not in module.__dict__, "Configuration identity helper collides with original source")
        def verify(freeze, executable):
            self.check_binding(freeze)
            self.check_binding(executable)
        module.__dict__[helper] = verify
        function.body[guards[0]] = ast.copy_location(ast.parse(helper + "(freeze, executable)").body[0],
                                                  function.body[guards[0]])
        rewritten = ast.fix_missing_locations(ast.Module(body=[function], type_ignores=[]))
        exec(compile(rewritten, str(self.inputs.path(name)), "exec"), module.__dict__)
        module.configuration._h0_configuration_identity = True
        self.adaptations[(name, "configuration")] = {
            "path": name, "function": "configuration", "original_function_ast_sha256": original_sha,
            "public_function_ast_sha256": sha(ast.dump(function).encode()),
            "removed_metadata_statement": ast.unparse(expected),
            "identity": "verified source-view bytes and registered source labels", "Git_ancestry_replayed": False}

    def controls(self, command):
        require(isinstance(command, (list, tuple)) and len(command) == 2 and command[0] == "python3",
                "Original consumer attempted an unaudited subprocess")
        name = self.name(command[1])
        require(name in ORIGINAL_CONTROL_TESTS, "Original consumer attempted an unaudited subprocess")
        stdout, stderr = io.StringIO(), io.StringIO()
        arguments, search_path = sys.argv, sys.path[:]
        source_roots = [self.inputs.root, *[view.root for view in self.inputs.historical]]
        def source_module(module):
            filename = getattr(module, "__file__", None)
            return filename and any(Path(filename).resolve().is_relative_to(root) for root in source_roots)
        # Munich hardware suites consume an explicit public-intake adapter.
        isolated = name in NIST_CONTROL_TESTS
        previous_modules = ({key: module for key, module in tuple(sys.modules.items()) if source_module(module)}
                            if isolated else {})
        try:
            # Original controls were separate Python processes. Their plain
            # imports must not inherit a previous consumer's same-named module.
            for key in previous_modules:
                del sys.modules[key]
            if isolated:
                sys.path[:] = [entry for entry in search_path if not any(Path(entry).resolve().is_relative_to(root)
                                                                       for root in source_roots)]
            sys.argv = [str(self.inputs.path(name))]
            sys.path.insert(0, str(self.inputs.path(name).parent))
            with redirect_stdout(stdout), redirect_stderr(stderr):
                try:
                    runpy.run_path(sys.argv[0], run_name="__main__")
                    code = 0
                except SystemExit as error:
                    code = error.code if isinstance(error.code, int) else 0 if error.code is None else 1
        finally:
            sys.argv = arguments
            sys.path[:] = search_path
            if isolated:
                for key, module in tuple(sys.modules.items()):
                    if source_module(module):
                        del sys.modules[key]
                sys.modules.update(previous_modules)
        self.adaptations[(name, "control-import-state")] = {
            "path": name, "source_module_cache_isolated": isolated,
            "original_parent_module_cache_restored": True, "source_modules_removed": len(previous_modules)}
        return subprocess.CompletedProcess(command, code, stdout.getvalue(), stderr.getvalue())


class VerifiedLoader(importlib.abc.Loader):
    def __init__(self, original, provider):
        self.original, self.provider = original, provider

    def create_module(self, spec):
        create = getattr(self.original, "create_module", None)
        return create(spec) if create else None

    def exec_module(self, module):
        self.provider.name(module.__spec__.origin)
        self.original.exec_module(module)
        self.provider.patch_module(module)


class VerifiedFinder(importlib.abc.MetaPathFinder):
    def __init__(self, provider):
        self.provider = provider

    def find_spec(self, fullname, path=None, target=None):
        spec = importlib.machinery.PathFinder.find_spec(fullname, path, target)
        if spec and spec.origin and Path(spec.origin).resolve().is_relative_to(self.provider.inputs.root):
            spec.loader = VerifiedLoader(spec.loader, self.provider)
            return spec
        return None


@contextmanager
def original_source_metadata(provider):
    factory = importlib.util.spec_from_file_location
    finder = VerifiedFinder(provider)
    def source_spec(name, location, *args, **kwargs):
        result = factory(name, location, *args, **kwargs)
        if result and result.loader and Path(location).resolve().is_relative_to(provider.inputs.root):
            result.loader = VerifiedLoader(result.loader, provider)
        return result
    previous_run, previous_output = subprocess.run, subprocess.check_output
    previous_loads = json.loads
    previous_decoders = lzma.decompress, gzip.decompress
    def recorded_json(raw, *args, **kwargs):
        result = previous_loads(raw, *args, **kwargs)
        encoded = raw.encode() if isinstance(raw, str) else raw
        digest = sha(encoded)
        if digest in provider.raw_identities or digest in provider.logical_hashes:
            provider.collect(result)
        return result
    def only_original_controls(command, *args, **kwargs):
        if isinstance(command, (list, tuple)) and len(command) == 2 and command[0] == "python3":
            return provider.controls(command)
        raise ReplayError("Original consumer attempted a Git/build/producer subprocess; this group is not publicly connected")
    sys.meta_path.insert(0, finder)
    importlib.util.spec_from_file_location = source_spec
    json.loads = recorded_json
    # A verified compressed receipt owns its decoded labels as directly as a
    # verified JSON file. Numerical consumers still receive the original bytes.
    lzma.decompress = provider.decoder("lzma.decompress", previous_decoders[0])
    gzip.decompress = provider.decoder("gzip.decompress", previous_decoders[1])
    subprocess.run = subprocess.check_output = only_original_controls
    try:
        yield
    finally:
        subprocess.run, subprocess.check_output = previous_run, previous_output
        json.loads = previous_loads
        lzma.decompress, gzip.decompress = previous_decoders
        importlib.util.spec_from_file_location = factory
        sys.meta_path.remove(finder)


def nist_consumers(inputs, check, output):
    consumers = check.get("consumers")
    require(isinstance(consumers, list) and consumers, "NIST needs explicit complete witness consumers")
    provider = RecordedSourceBindings(inputs, check.get("historical_bindings"))
    results, controls = [], []
    base = BELL + "/nist-real/nominal-replay/"
    with original_source_metadata(provider):
        for index, row in enumerate(consumers):
            path = relative(row["path"])
            require(path.startswith(base), "Unknown NIST source consumer")
            local = path[len(base):]
            require(local in NIST_CONSUMERS and row.get("function", NIST_CONSUMERS[local]) == NIST_CONSUMERS[local],
                    "Only audited full tree/interval consumer functions may run")
            module = inputs.load(path, "_h0_nist_consumer_" + str(index))
            provider.patch_module(module)
            function = getattr(module, NIST_CONSUMERS[local])
            if local == "observable-closure/verify_receiver.py":
                result = function(inputs.path(row["independent_report"]))
            else:
                result = function()
            validate_nist_certificate(local, module, result)
            write_json(output / ("consumer-" + str(index) + ".json"), result)
            results.append({"path": path, "function": NIST_CONSUMERS[local],
                            "fresh_output": "consumer-" + str(index) + ".json",
                            "result": result})
        selected_controls = check.get("controls", [])
        require(isinstance(selected_controls, list) and all(name in NIST_CONTROL_TESTS for name in selected_controls),
                "Unknown original NIST negative-control suite")
        for index, name in enumerate(selected_controls):
            completed = provider.controls(["python3", str(inputs.path(name))])
            (output / ("control-" + str(index) + ".stdout.log")).write_text(completed.stdout)
            (output / ("control-" + str(index) + ".stderr.log")).write_text(completed.stderr)
            require(completed.returncode == 0, "Original NIST negative controls failed: " + name)
            controls.append({"path": name, "exit_code": completed.returncode})
    require(results, "No NIST witness was checked")
    return {"consumers": results, "source_bindings": list(provider.used.values()),
            "focused_controls": controls,
            "metadata_adaptations": list(provider.adaptations.values()),
            "private_Git_or_build_used": False, "original_ancestry_replayed": False,
            "scope": "Original complete mathematical witness consumers; historical execution labels retained"}


def validate_nist_certificate(path, module, result):
    require(isinstance(result, dict) and isinstance(result.get("schema"), str) and result["schema"],
            "Full witness consumer returned no certificate")
    require(result.get("evidence_valid", True) is True, "Full witness consumer rejected its evidence")
    status = result.get("status", "")
    require(isinstance(status, str) and not any(word in status.lower() for word in
            ("failed", "unresolved", "disabled", "invalid")), "Full witness consumer did not certify the witness")
    for name in ("POSITIVE_FIELDS", "FLAGS", "POSITIVE"):
        fields = getattr(module, name, ())
        require(all(result.get(field) is True for field in fields), "Original complete witness flags are absent")
    if path == "observable-closure/full-statistical-fiber/verify_fiber.py":
        require(set(result.get("tree_verification", {})) == {"primary", "independent"} and
                set(result.get("member_verification", {})) == {"primary", "independent"} and
                {row["implementation"] for row in result.get("actual_Born_uniform_counterexamples", [])} ==
                {"primary", "independent"}, "Complete paired source trees/actual Born members were not checked")
    elif path == "public-review/source-compression/statistics_verify.py":
        require(len(result.get("records", [])) == 24 and all(len(row.get("conditional", [])) == 4 and
                all(len(setting) == 6 for setting in row["conditional"]) for row in result["records"]),
                "Complete 576 conditional probability intervals were not checked")
    elif path in {"public-review/source-compression/domain_verify.py", "public-review/source-compression/verify.py"}:
        require(isinstance(result.get("source_summary"), dict) and result["source_summary"] and
                Fraction(result.get("uniform_CH_N5_lower_bound", "0")) > 0,
                "Complete source-domain witness/positive CH bound is absent")
    elif path == "observable-closure/verify_slice.py":
        require(isinstance(result.get("primary_cover"), dict) and isinstance(result.get("independent_cover"), dict) and
                result.get("independent_Fock_cross", {}).get("complete_outcomes") == 16 and
                len(result.get("focused_tests", [])) == 2,
                "Complete scalar covers/full Fock slice controls are absent")
    elif path == "observable-closure/verify_receiver.py":
        require(type(result.get("scalar_segments_recomputed")) is int and result["scalar_segments_recomputed"] > 0 and
                result.get("all_boundaries_preserved") is True and
                isinstance(result.get("independent_Fock_gain"), dict) and
                result.get("focused_tests", {}).get("returncode") == 0,
                "Complete rounding-box/Fock receiver controls are absent")


def nominal_replay(inputs, check, output):
    base = BELL + "/nist-real/nominal-replay"
    require(check.get("root", base) == base, "Unexpected corrected nominal replay root")
    provider = RecordedSourceBindings(inputs, check.get("historical_bindings"), output)
    with original_source_metadata(provider):
        primary = inputs.load(base + "/replay.py", "_h0_nominal_primary")
        independent = inputs.load(base + "/independent_replay.py", "_h0_nominal_independent")
        consumer = inputs.load(BELL + "/nist-real/nominal_optimum.py", "_h0_nominal_consumer")
        frozen = primary.load_frozen()
        require(frozen == independent.load_frozen() and frozen["criterion_version"] == "nominal-replay-r0003",
                "Corrected criterion parsers disagree")
        original_primary = read_json(inputs.path(base + "/replay-r0003.json"))
        original_independent = read_json(inputs.path(base + "/independent_replay-r0003.json"))
        primary.REPLAY_PATH = str(output / "replay-r0003.json")
        independent.REPLAY_PATH = primary.REPLAY_PATH
        independent.OUT_PATH = str(output / "independent_replay-r0003.json")
        primary.main()
        require(independent.main() == 0, "Independent corrected 17-point replay failed")
        fresh_primary = read_json(output / "replay-r0003.json")
        fresh_independent = read_json(output / "independent_replay-r0003.json")
        instrument = read_json(inputs.path(BELL + "/nist-real/instrument.json"))
        original = consumer.assess_nominal_replay(instrument)
        fresh = consumer.assess_nominal_replay(instrument, report_dir=output)
        for result in (original, fresh):
            require(result.get("evidence_valid") is True and result.get("box_points_verified") == 17,
                    "Original nominal consumer rejected the full corrected replay")
        require(fresh["status"] == original["status"] and fresh["primary_verdict"] == original_primary["verdict"] and
                fresh["independent_verdict"] == original_independent["verdict"] and
                fresh["documented_values_in_band"] == original["documented_values_in_band"],
                "Corrected replay changed the original scientific verdict")
        tolerance = frozen["tolerance"]
        for now, old in ((fresh_primary, original_primary), (fresh_independent, original_independent)):
            require(len(now["box_points"]) == len(old["box_points"]) == 17, "Incomplete original corrected input box")
            for a, b in zip(now["box_points"], old["box_points"], strict=True):
                for key in consumer.POINT_KEYS:
                    require(a[key] == b[key], "Original corrected input point changed")
                for key in consumer.OPTIMUM_KEYS:
                    limit = tolerance["r" if key == "r" else "S_abs" if key == "S" else "angle_deg"]
                    require(consumer.close(a["optimum"][key], b["optimum"][key], limit),
                            "Corrected optimum differs beyond the original criterion tolerance")
        write_json(output / "consumer.json", fresh)
    return {"fresh_mathematical_points_per_implementation": 17,
            "original_frozen_verdict": original["status"], "fresh_verdict": fresh["status"],
            "documented_values_in_band": fresh["documented_values_in_band"],
            "apparatus_ready": fresh["verified"], "original_fixed_optimizers_executed": True,
            "source_bindings": list(provider.used.values()), "original_ancestry_replayed": False,
            "scope": "Corrected r0003 nominal model and original predeclared band; original negative outcome retained"}


def public_member(inputs, check, output):
    base = BELL + "/nist-real/nominal-replay/observable-prediction"
    require(check.get("root", base) == base, "Unexpected public member root")
    provider = RecordedSourceBindings(inputs, check.get("historical_bindings"), output)
    with original_source_metadata(provider):
        producer = inputs.load(base + "/public_compare_po0003.py", "_h0_public_member_primary")
        independent = inputs.load(base + "/public-witness-check.py", "_h0_public_member_independent")
        program = base + "/public-witness-check.py"
        def public_freeze():
            row = provider.binding(inputs.path(program), inputs.bindings[program]["source_revision"])
            return {"commit": row["commit"], "sha256": row["sha256"]}
        def public_specification():
            criterion = Path(independent.CRITERION)
            name = provider.name(criterion)
            provider.binding(criterion, inputs.bindings[name]["source_revision"])
            blocks = re.findall(r"```json\s*(.*?)\s*```", criterion.read_text(), re.S)
            require(len(blocks) == 1, "One original observable prediction specification is required")
            return json.loads(blocks[0])
        # These two helpers only located old Git bytes; the original source
        # constructor, intervals and full-modal checker execute unchanged.
        independent.executable_freeze = public_freeze
        independent.specification = public_specification
        primary = producer.run()
        frozen = read_json(inputs.path(base + "/public-comparison-po0003.json"))
        specification = public_specification()
        tolerance = float(Fraction(specification["probability_tolerance"]))
        close_numbers(primary, frozen, tolerance)
        write_json(output / "public-comparison-po0003.json", primary)
        result = independent.check_report(output / "public-comparison-po0003.json")
        require(result.get("passed") is True and result.get("input_version") == "p23-public-observables-po0003",
                "Original independent full-modal member check failed")
        require(primary.get("complete_trials") == 177358351 and primary.get("features_evaluated") == 12 and
                primary.get("held_out_count_access_in_member_construction") is False and
                primary.get("whole_held_out_row_change_leaves_training_identical") is True,
                "Original public complete-trial/held-out contract changed")
        require(len(result["branches"]) == 3 and [row["model"] for row in result["branches"]] ==
                ["S1_signal", "independent_OR", "named_M3"], "Public rate model inventory changed")
        for branch in result["branches"]:
            require(all(branch.get(name) is True for name in
                    ("independent_forward_validation_passed", "exact_interval_membership_certified",
                     "floating_point_membership_check")), "Full member or original CI inclusion failed")
            for name in ("actual_float_in_confidence", "theory_envelope_subset_confidence", "actual_float_in_theory_envelope"):
                require(set(branch[name]) == {"j", "sA_cell", "sB_cell"} and all(
                    len(row) == 4 and all(value is True for value in row) for row in branch[name].values()),
                    "Incomplete original twelve probability cells")
        old = read_json(inputs.path(base + "/public-witness-verification.json"))
        close_numbers(result["branches"], old["branches"], tolerance)
        write_json(output / "public-witness-verification.json", result)
    return {"models_checked": 3, "full_probability_cells_per_model": 12, "complete_trials": 177358351,
            "held_out_row": 2, "original_source_member_constructor_executed": True,
            "independent_full_modal_forward_executed": True,
            "source_mapping_identified": False, "publication_configuration_identified": False,
            "source_bindings": list(provider.used.values()), "original_ancestry_replayed": False,
            "scope": "Original po0003 public complete-count training/member/held-out contract"}


def verified_source_rows(provider, rows):
    require(isinstance(rows, list), "Kernel source bindings are absent")
    for row in rows:
        require(isinstance(row, dict) and isinstance(row.get("path"), str), "Invalid kernel source binding")
        path = provider.inputs.path(relative(row["path"]))
        require(provider.digest(path) == row.get("sha256"), "Paid kernel source identity changed: " + row["path"])
        if "commit" in row:
            provider.check_binding(row)


def paid_anchor_kernel(inputs, provider, anchors):
    path = BELL + "/munich/readout-domain/anchors-certification-first.json"
    report = read_json(inputs.path(path))
    anchors.validate_payload(report)
    verified_source_rows(provider, report["source_bindings"])
    return report


@contextmanager
def hardware_anchor_intake(inputs, provider, science):
    parent, anchors = science.parent, science.anchors_certify
    originals = parent.frozen, parent.sha256, anchors.consume, science.consume
    previous_module = sys.modules.get("hardware_anchors_run")
    def public_frozen(path, commit="HEAD"):
        name = provider.name(path)
        if commit != "HEAD":
            provider.binding(inputs.path(name), commit)
        return inputs.path(name).read_bytes()
    def public_kernel(certificate=None, *, require_frozen=True):
        canonical = inputs.path(BELL + "/munich/readout-domain/anchors-certification-first.json")
        require(certificate is None or Path(certificate).read_bytes() == canonical.read_bytes(),
                "Anchor override changes canonical receipt")
        return paid_anchor_kernel(inputs, provider, anchors)
    def public_consume(certificate=None):
        base = BELL + "/munich/readout-domain/"
        path = inputs.path(base + "hardware-anchors-first.json") if certificate is None else Path(certificate)
        report = parent.strict_json(path.read_bytes())
        raw = public_frozen(inputs.path(base + "hardware-anchors-attempt.json"))
        attempt = parent.strict_json(raw)
        parent.require(report["attempt_sha256"] == provider.digest(raw) and
                report["freeze_commit"] == attempt["freeze_commit"] and
                report["execution_head"] == attempt["execution_head"] and
                report["source_bindings"] == attempt["source_bindings"] == science.bindings(report["freeze_commit"]),
                "Hardware anchor first identity changed")
        rebuilt = science.controls()
        rebuilt.update({name: report[name] for name in ("freeze_commit", "execution_head", "attempt_sha256", "source_bindings")})
        parent.require(parent.canonical(rebuilt) == parent.canonical(report), "Hardware anchor construction receipt changed")
        return report
    parent.frozen, parent.sha256 = public_frozen, provider.digest
    anchors.consume, science.consume = public_kernel, public_consume
    sys.modules["hardware_anchors_run"] = science
    try:
        yield
    finally:
        parent.frozen, parent.sha256, anchors.consume, science.consume = originals
        if previous_module is None:
            sys.modules.pop("hardware_anchors_run", None)
        else:
            sys.modules["hardware_anchors_run"] = previous_module


def munich_contract(inputs, check, output):
    base = BELL + "/munich/readout-domain"
    require(check.get("root", base) == base and check.get("contract") in MUNICH_CONTRACTS,
            "Unknown complete Munich source contract")
    contract = check["contract"]
    names = MUNICH_CONTRACTS[contract]
    provider = RecordedSourceBindings(inputs, fresh_root=output)
    with original_source_metadata(provider), ExitStack() as adapters:
        consumer = inputs.load(base + "/" + names[0], "_h0_munich_contract_consumer")
        load = lambda name: read_json(inputs.path(base + "/" + name))
        if contract != "hardware-anchors":
            primary, checked = [load(name) for name in consumer.FIRSTS]
        fresh = {}
        if contract == "hardware-anchors":
            adapters.enter_context(hardware_anchor_intake(inputs, provider, consumer))
            fresh = consumer.consume()
        elif contract == "identification":
            witness, counts = load("primitive-witness-c0002.json"), load("primary-first-c0002.json")
            checker = inputs.load(base + "/identification_independent.py", "_h0_identity_independent")
            rebuilt = checker.check_primary(primary, witness, counts)
            require(all(checked.get(key) == value for key, value in rebuilt.items()),
                    "Independent complete quotient/fibre/projection changed")
            validated = consumer.validate(primary, checked, witness, counts)
            fresh = {"independent": rebuilt, "validated": validated}
        elif contract in {"shared-response", "joint-response"}:
            counts, biases = load("primary-first-c0002.json"), load("identification-first.json")
            if contract == "shared-response":
                previous = load("response-projection-first.json")
                fresh = consumer.validate(primary, checked, counts, biases, previous)
            else:
                shared, primitive = load("shared-response-first.json"), load("primitive-witness-c0002.json")
                fresh = consumer.validate(primary, checked, counts, biases, shared, primitive)
        elif contract == "atomic-forward":
            science = consumer.science
            producer = inputs.load(base + "/atomic_forward.py", "_h0_atomic_primary")
            checker = inputs.load(base + "/atomic_forward_independent.py", "_h0_atomic_independent")
            responses = []
            for old, other, (name, values) in zip(primary["samples"], checked["samples"], science.SAMPLES, strict=True):
                raw = [dict(zip(science.KEYS, values))]
                left = producer.propagate((producer.Pulse(*values),))
                right = checker.propagate(raw)
                require(old["id"] == other["id"] == name and left == old["response"] and right == other["response"],
                        "Original fixed atomic interval propagation changed")
                science.validate_intervals(left, primary=True)
                science.validate_intervals(right, primary=False)
                checker.verify_intersection(left, right)
                responses.append({"id": name, "primary": left, "independent": right})
            separated = consumer.validate(primary, checked)
            dose = inputs.load(base + "/atomic_dose.py", "_h0_atomic_dose")
            shared, joint = load("shared-response-first.json"), load("joint-response-first.json")
            dose_bounds = [{"run": a["run"], **dose.bounds(a, b)}
                           for a, b in zip(shared["runs"], joint["runs"], strict=True)]
            require(dose_bounds == primary["kinetic_dose_bounds"] == checked["kinetic_dose_bounds"],
                    "Original whole-confidence kinetic dose bounds changed")
            fresh = {"samples": responses, "kinetic_dose_bounds": dose_bounds,
                     "theory_unequal_trace_control_certified": separated,
                     "fresh_primary_forward_samples": 4, "fresh_independent_forward_samples": 4,
                     "restriction_coefficient_checks": 12288, "response_intersections_checked": 12}
        elif contract == "detector-fiber":
            original = [load(name) for name in ("shared-response-first.json", "identification-first.json",
                                               "joint-response-first.json", "atomic-forward-first.json")]
            left = consumer.science.build(*original, "primary")
            right = consumer.science.build(*original, "independent")
            require(left == right, "Complete detector inverse/polygon/whole-confidence implementations disagree")
            fresh = consumer.validate(primary, checked, right)
        else:
            witness = load("primitive-witness-c0002.json")
            fresh = consumer.validate(primary, checked, witness)
            primary_image = consumer.science.realizations(primary["samples"], witness, "primary")
            require(primary_image == fresh, "Complete physical pulse image/response fibres disagree")
        write_json(output / "mathematical-consumer.json", fresh)
        controls = []
        for name in names[1:]:
            result = provider.controls(["python3", str(inputs.path(base + "/" + name))])
            (output / (name + ".stdout.log")).write_text(result.stdout)
            (output / (name + ".stderr.log")).write_text(result.stderr)
            require(result.returncode == 0, "Original source-contract negative controls failed: " + name)
            controls.append({"path": base + "/" + name, "exit_code": result.returncode})
    return {"contract": contract, "original_mathematical_consumer": base + "/" + names[0] +
            ("::controls" if contract == "hardware-anchors" else "::validate"),
            "mathematical_output": "mathematical-consumer.json", "focused_controls": controls,
            "original_first_receipts_overwritten": False, "fresh_Lean_certification_executed": False,
            "private_Git_or_build_used": False, "original_ancestry_replayed": False,
            "source_bindings": list(provider.used.values()),
            "kernel_dependency_history_replayed": False,
            "kernel_gate": "public Lean package acceptance" if contract == "hardware-anchors" else "separate Lean package acceptance",
            "scope": "Complete named original mathematical source contract and its original negative controls"}


def quantum_command(check, output, executable):
    command = [executable, str(ROOT / "tools/first_release_quantum.py"),
               "--config", str(inside(ROOT, check["quantum_config"])),
               "--output", str(output / "quantum"), "--python", executable]
    if check.get("ids") is not None:
        command.extend(["--ids", *check["ids"]])
    return command


def quantum_independent(check, output, executable, map_sha256):
    # The child owns its per-carrier views and input audit; this worker verifies
    # coverage and the real process exit against that independent report.
    import first_release_quantum as quantum
    config_path = inside(ROOT, check["quantum_config"])
    config_sha = sha(config_path.read_bytes())
    require(config_sha == check["quantum_config_sha256"], "Quantum configuration changed")
    config = quantum.load_config(config_path)
    ids = check.get("ids")
    require(ids is None or set(ids) <= {row["id"] for row in config["checks"]}, "Unknown selected quantum id")
    expected = [row["id"] for row in config["checks"] if ids is None or row["id"] in ids]
    require(expected, "Quantum carrier selection is empty")
    program = ROOT / "tools/first_release_quantum.py"
    program_sha = sha(program.read_bytes())
    command = quantum_command(check, output, executable)
    completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, check=False,
                               timeout=check.get("timeout_seconds", 21600))
    (output / "quantum.stdout.log").write_text(completed.stdout)
    (output / "quantum.stderr.log").write_text(completed.stderr)
    require(sha(config_path.read_bytes()) == config_sha and sha(program.read_bytes()) == program_sha,
            "Quantum configuration or runner changed during execution")
    report = read_json(output / "quantum/report.json")
    require(report.get("schema") == quantum.REPORT_SCHEMA, "Unknown independent quantum report")
    require(report.get("config_sha256") == config_sha and report.get("map_sha256") == map_sha256,
            "Independent quantum run used a different configuration or export identity")
    rows = report.get("checks")
    require(isinstance(rows, list) and len(rows) == len(expected) and
            all(isinstance(row, dict) for row in rows) and
            {row.get("id") for row in rows} == set(expected) and report.get("selected") == expected,
            "Independent quantum report omitted or duplicated a selected carrier")
    require(type(report.get("exit_code")) is int and report["exit_code"] == completed.returncode,
            "Independent quantum report and actual process exit disagree")
    failed = [row["id"] for row in rows if row.get("status") != "passed" or
              type(row.get("exit_code")) is not int or row["exit_code"] != 0 or
              type(row.get("actual_process_exit_code")) is not int or row["actual_process_exit_code"] != 0]
    require(completed.returncode == 0 and report.get("status") == "passed" and not failed,
            "Original independent quantum checks failed: " + ", ".join(failed))
    complete = set(expected) == set(config["required"])
    require(report.get("complete_carrier_scope") is complete,
            "Independent quantum carrier scope disagrees with the requested selection")
    return {"scope": expected, "complete_carrier_scope": complete,
            "child_report": "quantum/report.json", "actual_process_exit_code": completed.returncode,
            "quantum_config": {"path": check["quantum_config"], "sha256": config_sha},
            "runner": {"path": "tools/first_release_quantum.py", "sha256": program_sha},
            "map_sha256": map_sha256, "original_independent_programs_executed": True}


def execute_worker(spec):
    map_snapshot = Path(spec["map_snapshot"])
    require(map_snapshot.resolve().is_relative_to((ROOT / ".local").resolve()) and
            sha(map_snapshot.read_bytes()) == spec["map_sha256"], "Public export-map snapshot changed")
    check, output = spec["check"], Path(spec["output"])
    require(output.resolve().is_relative_to((ROOT / ".local").resolve()), "Worker output is outside .local")
    require(not output.exists(), "Worker output already exists; the original execution is retained")
    output.mkdir(parents=True)
    view = spec.get("view")
    if view is not None:
        require(Path(view["root"]).resolve().is_relative_to((ROOT / ".local").resolve()),
                "Worker source view is outside the public task directory")
        for historical in view.get("historical_views", []):
            require(Path(historical["root"]).resolve().is_relative_to(map_snapshot.parent.resolve()),
                    "Historical source view is outside its explicit public task directory")
    inputs = None if view is None else PublicInputs(Path(view["root"]), view["bindings"], view.get("historical_views", []))
    if inputs:
        inputs.verify_all()
    kind = check["kind"]
    archive_dir = Path(spec["archive_dir"]) if spec.get("archive_dir") else None
    started = time.monotonic()
    try:
        worker_input_scope(spec, output, inputs)
        if kind in {"core-identities", "fock-current", "exact-source-controls"}:
            result = run_program(inputs, check, output, spec["python"])
        elif kind == "theory-blind":
            result = blind_born(inputs, check, output)
        elif kind == "eth-bell":
            result = eth_bell(inputs, check, output, archive_dir)
        elif kind == "munich-bell":
            result = munich_bell(inputs, check, output, archive_dir)
        elif kind == "nist-witness-consumers":
            result = nist_consumers(inputs, check, output)
        elif kind == "nist-nominal-replay":
            result = nominal_replay(inputs, check, output)
        elif kind == "nist-public-member":
            result = public_member(inputs, check, output)
        elif kind == "munich-contract":
            result = munich_contract(inputs, check, output)
        elif kind == "quantum-independent":
            result = quantum_independent(check, output, spec["python"], spec["map_sha256"])
        else:
            raise ReplayError("Unknown worker check")
        if inputs:
            # Generated outputs were omitted from the immutable view manifest.
            inputs.verify_all()
        files = [{"path": path.relative_to(output).as_posix(), "sha256": sha(path.read_bytes()),
                  "bytes": path.stat().st_size} for path in sorted(output.rglob("*")) if path.is_file()]
        receipt = {"id": check["id"], "kind": kind, "status": "passed", "exit_code": 0,
                   "elapsed_seconds": time.monotonic() - started, "result": result, "output_files": files}
    except Exception as error:
        receipt = {"id": check["id"], "kind": kind, "status": "failed", "exit_code": 1,
                   "elapsed_seconds": time.monotonic() - started,
                   "error": {"type": type(error).__name__, "reason": str(error)}}
    write_json(output / "execution.json", receipt)
    return receipt


def run(config_path, mode, output=None, archive_dir=None, python=sys.executable):
    config_path = Path(config_path)
    require(config_path.resolve().is_relative_to(ROOT.resolve()), "Runtime config must be in this repository")
    config = load_config(config_path)
    checks = select_checks(config, mode)
    python = python_executable(python)
    directory = output or ROOT / ".local/first-release-replay" / (mode + "-" + uuid.uuid4().hex[:12])
    directory = Path(directory).resolve()
    require(directory.is_relative_to((ROOT / ".local").resolve()) and not directory.exists(),
            "Replay output must be a new task directory under .local")
    directory.mkdir(parents=True)
    map_bytes = (ROOT / "tools/export-map.json").read_bytes()
    map_sha = sha(map_bytes)
    map_snapshot = directory / "export-map.snapshot.json"
    map_snapshot.write_bytes(map_bytes)
    report = {"schema": REPORT_SCHEMA, "mode": mode, "started_at": datetime.now(timezone.utc).isoformat(),
              "config_sha256": sha(config_path.read_bytes()), "map_sha256": map_sha,
              "Lean_build_executed": False, "old_scientific_execution_overwritten": False,
              "historical_execution_head_is_a_recorded_identity": True, "views": {}, "checks": []}
    started = time.monotonic()
    for check in checks:
        output_dir = directory / "checks" / check["id"]
        view = None
        try:
            if check["kind"] not in {"core-identities", "quantum-independent"}:
                view_id = check["view"]
                require(re.fullmatch(r"[a-z0-9][a-z0-9_-]*", view_id), "Invalid source-view id")
                if view_id not in report["views"]:
                    omit = [row["output"] for row in checks if row.get("view") == view_id and
                            row["kind"] == "exact-source-controls"]
                    metadata = prepare_view(ROOT, directory / "views" / view_id, config["views"][view_id], omit,
                                            map_snapshot)
                    report["views"][view_id] = metadata
                view = {**report["views"][view_id], "root": str(directory / "views" / view_id)}
                view["historical_views"] = []
                for historical_id in check.get("historical_views", []):
                    require(re.fullmatch(r"[a-z0-9][a-z0-9_-]*", historical_id), "Invalid historical source-view id")
                    if historical_id not in report["views"]:
                        report["views"][historical_id] = prepare_view(
                            ROOT, directory / "views" / historical_id, config["views"][historical_id], export_map=map_snapshot)
                    view["historical_views"].append({**report["views"][historical_id],
                                                   "root": str(directory / "views" / historical_id)})
            inputs = []
            for row in check.get("inputs", []):
                path = inside(ROOT, row["path"])
                raw = path.read_bytes()
                require(sha(raw) == row["sha256"], "Explicit runtime input changed")
                inputs.append({"path": row["path"], "sha256": sha(raw), "bytes": len(raw)})
            frozen = check.get("frozen")
            worker_check = dict(check)
            if frozen:
                path = inside(ROOT, frozen)
                require(path.is_file(), "Frozen comparison receipt is missing")
                raw = path.read_bytes()
                worker_check["frozen_sha256"] = sha(raw)
                inputs.append({"path": frozen, "sha256": sha(raw), "bytes": len(raw), "role": "frozen_comparison"})
            if check["kind"] == "quantum-independent":
                path = inside(ROOT, check["quantum_config"])
                raw = path.read_bytes()
                worker_check["quantum_config_sha256"] = sha(raw)
                inputs.append({"path": check["quantum_config"], "sha256": sha(raw), "bytes": len(raw),
                               "role": "independent_quantum_configuration"})
            spec = {"check": worker_check, "output": str(output_dir), "view": view, "map_sha256": map_sha,
                    "map_snapshot": str(map_snapshot),
                    "archive_dir": str(Path(archive_dir).resolve()) if archive_dir else None, "python": python}
            spec_path = directory / (check["id"] + ".worker.json")
            write_json(spec_path, spec)
            command = [python, str(Path(__file__).resolve()), "_worker", str(spec_path)]
            elapsed = time.monotonic()
            completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, check=False,
                                       timeout=check.get("timeout_seconds", 21600))
            output_dir.mkdir(parents=True, exist_ok=True)
            (output_dir / "worker.stdout.log").write_text(completed.stdout)
            (output_dir / "worker.stderr.log").write_text(completed.stderr)
            receipt = read_json(output_dir / "execution.json")
            require(receipt["exit_code"] == completed.returncode and receipt["id"] == check["id"],
                    "Worker result and actual process exit disagree")
            receipt.update({"actual_process_exit_code": completed.returncode,
                            "command": [python, "tools/first_release_replay.py", "_worker", spec_path.relative_to(ROOT).as_posix()],
                            "process_elapsed_seconds": time.monotonic() - elapsed, "input_sha256": inputs,
                            "output_directory": output_dir.relative_to(ROOT).as_posix()})
        except Exception as error:
            receipt = {"id": check["id"], "kind": check["kind"], "status": "failed", "exit_code": 1,
                       "error": {"type": type(error).__name__, "reason": str(error)}}
        report["checks"].append(receipt)
        print(f"{check['id']}: {receipt['status']}", flush=True)
    report.update({"status": "passed" if all(row["status"] == "passed" for row in report["checks"]) else "failed",
                   "elapsed_seconds": time.monotonic() - started,
                   "scope": [row["id"] for row in checks]})
    write_json(directory / "report.json", report)
    return report, directory


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=("entry", "bell", "full", "_worker"))
    parser.add_argument("worker_spec", nargs="?")
    parser.add_argument("--config", type=Path, default=ROOT / "checks/first-release-runtime.json")
    parser.add_argument("--output", type=Path)
    parser.add_argument("--archive-dir", type=Path)
    parser.add_argument("--python", default=sys.executable)
    args = parser.parse_args(argv)
    try:
        if args.mode == "_worker":
            require(args.worker_spec is not None, "Worker specification is missing")
            spec_path = Path(args.worker_spec).resolve()
            require(spec_path.is_relative_to((ROOT / ".local").resolve()), "Worker specification must be under .local")
            result = execute_worker(read_json(spec_path))
            return result["exit_code"]
        result, path = run(args.config, args.mode, args.output, args.archive_dir, args.python)
        print(json.dumps({"status": result["status"], "report": path.relative_to(ROOT).as_posix() + "/report.json"}))
        return 0 if result["status"] == "passed" else 1
    except (ReplayError, OSError, ValueError) as error:
        print(json.dumps({"status": "failed", "error": str(error)}))
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
