#!/usr/bin/env python3
"""Run one named living-law runtime.

Micro and inquiry modes check a finite dependent readout in Lean.
Terminal peace runs the registered Lean process in batch or JSON worker mode.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sqlite3
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

from proposition_dependency_inventory import (
    active_lake_roots,
    closure,
    collect_modules,
)


LEAN_NAME_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$"
)
MICRO_KIND_PREFIX = "LivingRuntimeStructuralKind."
INQUIRY_KIND_PREFIX = "InquiryResolutionKind."
MAX_FUEL = 1000
TERMINAL_PEACE_TRACK = "SaturationMonoid.Tracks.LivingLawTerminalPeaceInstance"
TERMINAL_PEACE_BACKEND = (
    "SaturationMonoid/ProcessGame/Society/Institutions/Conflict/"
    "Constitution/TerminalPeace/Deployment/Main.lean"
)


@dataclass(frozen=True)
class RuntimeStep:
    index: int
    kind: str


def checked_lean_name(parser: argparse.ArgumentParser, label: str, value: str) -> str:
    if LEAN_NAME_RE.fullmatch(value) is None:
        parser.error(f"{label} must be an ASCII qualified Lean name")
    return value


def ensure_active_module(
    parser: argparse.ArgumentParser, lean_root: Path, module: str
) -> None:
    modules, imports = collect_modules(lean_root)
    if module not in modules:
        parser.error(f"unknown local Lean module: {module}")
    active = set().union(
        *(closure(root, imports) for _label, root in active_lake_roots(lean_root))
    )
    if module not in active:
        parser.error(
            f"module is not reachable from LivingLawActive: {module}"
        )


def render_micro_probe(module: str, facade: str, fuel: int) -> tuple[str, int]:
    lines = [
        f"import {module}",
        "",
        "set_option autoImplicit false",
        "",
        "open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution",
        "open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot",
        "",
        "namespace LivingLawRuntimeProbe",
        "",
        "noncomputable section",
        "",
        f"def facade := {facade}",
        "def runtime0 := facade.seed",
        f"def observedHistory := runtime0.run {fuel}",
        "",
    ]

    for index in range(fuel):
        runtime = f"runtime{index}"
        tick = f"tick{index}"
        next_runtime = f"runtime{index + 1}"
        lines.extend(
            [
                f"def {tick} := {runtime}.tick",
                f"def {next_runtime} := {tick}.next",
                "",
                f"example : facade.process.toAnswerNextCausalWorld.emitted",
                f"    (ULift.up {runtime}.state) = ULift.up {tick}.generated :=",
                f"  {runtime}.tick_occurrence_eq",
                "",
                f"example : HEq {tick}.generated.wholeLedgerWriteBack",
                f"    ({runtime}.current.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt",
                f"      {runtime}.current.visit.current) :=",
                f"  {tick}.generated.wholeLedgerWriteBack_eq",
                "",
                f"example : {tick}.nextCurrent =",
                f"    facade.process.stateAt (facade.process.successor {runtime}.state) :=",
                f"  {runtime}.tick_nextCurrent_eq",
                "",
                f"example (face : facade.FaceAt {runtime}) : True := by",
                f"  have _factorization := facade.readoutAt_factorizes {runtime} face",
                "  trivial",
                "",
                f"#reduce {tick}.structuralKind",
                "",
            ]
        )

    lines.extend(["end", "end LivingLawRuntimeProbe", ""])
    return "\n".join(lines), fuel


def render_inquiry_probe(module: str, runtime: str, fuel: int) -> tuple[str, int]:
    lines = [
        f"import {module}",
        "",
        "set_option autoImplicit false",
        "",
        "open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution",
        "open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot",
        "open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion",
        "",
        "namespace LivingLawInquiryRuntimeProbe",
        "",
        "noncomputable section",
        "",
        f"def runtime := {runtime}",
        f"def observedHistory := runtime.run {fuel}",
        "",
    ]

    for index in range(fuel):
        state = f"state{index}"
        tick = f"tick{index}"
        answer = f"answer{index}"
        receipt = f"receipt{index}"
        next_engine = f"nextEngine{index}"
        next_query = f"nextQuery{index}"
        lines.extend(
            [
                f"def {state} := runtime.stateAt {index}",
                f"def {tick} := runtime.tickAt {index}",
                f"def {answer} := {tick}.answer",
                f"def {receipt} := {tick}.receipt",
                f"def {next_engine} := {tick}.next",
                f"def {next_query} := (runtime.stateAt {index + 1}).activation.query",
                "",
                "example : True := by",
                f"  have _canonical := {tick}.eq_tick",
                f"  have _resolution := {tick}.resolution_eq_generated",
                f"  have _next := {tick}.next_erases_to_generated",
                f"  have _livingLaw := {tick}.next_preservesGeneratedLivingLaw",
                f"  have _stateStep := runtime.stateAt_succ {index}",
                f"  have _engineStep := runtime.stateAt_succ_engine {index}",
                f"  have _activationStep := runtime.stateAt_succ_activation {index}",
                "  trivial",
                "",
                f"#reduce {tick}.resolutionKind",
                "",
            ]
        )

    lines.extend(["end", "end LivingLawInquiryRuntimeProbe", ""])
    return "\n".join(lines), fuel


def parse_lean_json(
    output: str, expected_kinds: int, kind_prefix: str
) -> tuple[list[RuntimeStep], list[str]]:
    kinds: list[str] = []
    diagnostics: list[str] = []
    for raw_line in output.splitlines():
        try:
            message = json.loads(raw_line)
        except json.JSONDecodeError:
            if raw_line.strip():
                diagnostics.append(raw_line)
            continue
        data = str(message.get("data", ""))
        severity = message.get("severity")
        if severity == "information" and data.startswith(kind_prefix):
            kinds.append(data.removeprefix(kind_prefix))
        elif severity in {"warning", "error"}:
            position = message.get("pos", {})
            diagnostics.append(
                f"{severity} at {position.get('line', '?')}:"
                f"{position.get('column', '?')}: {data}"
            )
    if len(kinds) != expected_kinds:
        raise RuntimeError(
            "Lean did not expose exactly one source-derived kind "
            f"per tick (expected {expected_kinds}, got {len(kinds)})"
        )
    return [RuntimeStep(index, kind) for index, kind in enumerate(kinds)], diagnostics


def run_probe(
    lean_root: Path,
    source: str,
    expected_kinds: int,
    timeout: float,
    keep_probe: bool,
    kind_prefix: str,
) -> tuple[list[RuntimeStep], list[str], Path | None]:
    scratch = lean_root / "scratch"
    scratch.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        "w",
        suffix=".lean",
        prefix="living-runtime-",
        dir=scratch,
        encoding="utf-8",
        delete=False,
    ) as probe:
        probe.write(source)
        probe_path = Path(probe.name)
    relative_probe = probe_path.relative_to(lean_root)
    try:
        result = subprocess.run(
            ["lake", "env", "lean", "--json", str(relative_probe)],
            cwd=lean_root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            timeout=timeout,
        )
        if result.returncode != 0:
            excerpt = result.stdout[-8000:]
            raise RuntimeError(
                "runtime integration probe failed; this is a Lean/tooling "
                f"failure, not a world obstruction\n{excerpt}"
            )
        steps, diagnostics = parse_lean_json(
            result.stdout, expected_kinds, kind_prefix
        )
        return steps, diagnostics, probe_path if keep_probe else None
    finally:
        if not keep_probe:
            probe_path.unlink(missing_ok=True)


def git_metadata(repository_root: Path) -> tuple[str, bool]:
    head = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=repository_root,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    ).stdout.strip()
    dirty = bool(
        subprocess.run(
            ["git", "status", "--porcelain"],
            cwd=repository_root,
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        ).stdout.strip()
    )
    return head, dirty


def inquiry_capsule(
    lean_root: Path,
    module: str,
    runtime: str,
    fuel: int,
    source: str,
    steps: list[RuntimeStep],
) -> dict[str, object]:
    git_head, dirty = git_metadata(lean_root.parent)
    payload: dict[str, object] = {
        "schema": "living-law-inquiry-runtime-capsule/v1",
        "authority": "presentation-only",
        "module": module,
        "runtime": runtime,
        "fuel": fuel,
        "git_head": git_head,
        "dirty": dirty,
        "probe_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest(),
        "steps": [
            {
                "index": step.index,
                "resolution_kind": step.kind,
                "state_term": f"({runtime}).stateAt {step.index}",
                "query_term": (
                    f"(({runtime}).stateAt {step.index}).activation.query"
                ),
                "occurrence_term": f"({runtime}).tickAt {step.index}",
                "resolution_term": (
                    f"(({runtime}).tickAt {step.index}).resolution"
                ),
                "answer_term": f"(({runtime}).tickAt {step.index}).answer",
                "receipt_term": f"(({runtime}).tickAt {step.index}).receipt",
                "next_term": f"(({runtime}).tickAt {step.index}).next",
                "next_query_term": (
                    f"(({runtime}).stateAt {step.index + 1}).activation.query"
                ),
            }
            for step in steps
        ],
        "resume_command": (
            "python3 scripts/living_law_runtime.py "
            f"--module {module} --inquiry-runtime {runtime} --fuel {fuel}"
        ),
    }
    canonical = json.dumps(payload, ensure_ascii=False, sort_keys=True).encode("utf-8")
    payload["capsule_sha256"] = hashlib.sha256(canonical).hexdigest()
    return payload


def terminal_peace_command(root: Path, timeout: float, library: Path | None = None):
    command = ["lake", "env"]
    if library is not None:
        command = ["env", f"LEAN_PATH={library.resolve(strict=True)}"]
    elif overlay := os.environ.get("LEAN_PATH"):
        # Keep an explicitly selected deployment closure ahead of the Lake cache.
        search = subprocess.check_output(
            ["lake", "env", "printenv", "LEAN_PATH"], cwd=root, text=True, timeout=timeout
        ).strip()
        command.extend(["env", f"LEAN_PATH={overlay}{os.pathsep}{search}"])
    return command + ["lean", "--trust=0", "-j1", "-DwarningAsError=true", "-DElab.async=false",
                      "--run", TERMINAL_PEACE_BACKEND]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--module", help="active Lean module to import")
    entry = parser.add_mutually_exclusive_group(required=True)
    entry.add_argument(
        "--facade", help="fully qualified named fixed-root runtime facade"
    )
    entry.add_argument(
        "--inquiry-runtime",
        help="fully qualified named canonical inquiry runtime",
    )
    entry.add_argument(
        "--terminal-peace",
        action="store_true",
        help="run the registered terminal-peace deployment",
    )
    parser.add_argument(
        "--worker",
        action="store_true",
        help="serve terminal-peace JSON lines on stdin and stdout",
    )
    parser.add_argument(
        "--state",
        type=Path,
        help="resume a terminal-peace worker from its committed original inputs",
    )
    parser.add_argument(
        "--admission", type=Path,
        help="pin the durable terminal-peace journal to its owner and four native verifiers",
    )
    parser.add_argument("--library", type=Path, help="use an installed terminal-peace Lean import closure")
    parser.add_argument(
        "--fuel",
        type=int,
        help="number of canonical ticks to observe (default: 3)",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        help="Lean process timeout in seconds (default: 120 for finite runs)",
    )
    parser.add_argument(
        "--keep-probe", action="store_true", help="retain the generated Lean probe"
    )
    parser.add_argument(
        "--capsule-output",
        type=Path,
        help="write a deterministic inquiry trace capsule as JSON",
    )
    args = parser.parse_args()

    if args.capsule_output is not None and args.inquiry_runtime is None:
        parser.error("--capsule-output requires --inquiry-runtime")
    if args.worker and (not args.terminal_peace or args.fuel is not None):
        parser.error("--worker requires --terminal-peace and uses requests instead of --fuel")
    if args.state is not None and not (args.terminal_peace and args.worker):
        parser.error("--state requires --terminal-peace --worker")
    if args.admission is not None and args.state is None:
        parser.error("--admission requires --terminal-peace --worker --state")
    if args.library is not None and not args.terminal_peace:
        parser.error("--library requires --terminal-peace")
    if args.fuel is None:
        args.fuel = 3
    if args.fuel < 0:
        parser.error("--fuel must be nonnegative")
    if args.fuel > MAX_FUEL:
        parser.error(f"--fuel must not exceed {MAX_FUEL}; run bounded batches instead")
    if args.timeout is not None and not 0 < args.timeout < float("inf"):
        parser.error("--timeout must be positive")
    timeout = args.timeout if args.timeout is not None else 120.0

    lean_root = Path(__file__).resolve().parents[1]
    if args.terminal_peace:
        if args.module is not None or args.keep_probe:
            parser.error("--terminal-peace uses its registered module and native backend")
        if not any(root == TERMINAL_PEACE_TRACK for _, root in active_lake_roots(lean_root)):
            parser.error("terminal-peace deployment is not registered in LivingLawActive")
        try:
            command = terminal_peace_command(lean_root, timeout, args.library)
            if args.state is not None:
                from terminal_peace_worker import serve

                serve(command + ["--live"], lean_root, Path(TERMINAL_PEACE_BACKEND),
                      args.state.resolve(), timeout, args.admission)
                return
            mode = ["--worker"] if args.worker else ["--fuel", str(args.fuel)]
            result = subprocess.run(
                command + mode,
                cwd=lean_root,
                timeout=args.timeout if args.worker else timeout,
            )
        except (OSError, subprocess.SubprocessError, sqlite3.Error, ValueError, RuntimeError) as error:
            print(f"living-law runtime integration failure: {error}", file=sys.stderr)
            raise SystemExit(1) from error
        if result.returncode:
            raise SystemExit(result.returncode)
        return

    if args.module is None:
        parser.error("--module is required with --facade or --inquiry-runtime")
    module = checked_lean_name(parser, "--module", args.module)
    facade = (
        checked_lean_name(parser, "--facade", args.facade)
        if args.facade is not None
        else None
    )
    inquiry_runtime = (
        checked_lean_name(parser, "--inquiry-runtime", args.inquiry_runtime)
        if args.inquiry_runtime is not None
        else None
    )
    ensure_active_module(parser, lean_root, module)
    if facade is not None:
        source, expected_kinds = render_micro_probe(module, facade, args.fuel)
        kind_prefix = MICRO_KIND_PREFIX
        entry_kind = "micro"
        entry_name = facade
    else:
        assert inquiry_runtime is not None
        source, expected_kinds = render_inquiry_probe(
            module, inquiry_runtime, args.fuel
        )
        kind_prefix = INQUIRY_KIND_PREFIX
        entry_kind = "inquiry"
        entry_name = inquiry_runtime
    try:
        steps, diagnostics, retained_probe = run_probe(
            lean_root,
            source,
            expected_kinds,
            timeout,
            args.keep_probe,
            kind_prefix,
        )
    except (OSError, subprocess.TimeoutExpired, RuntimeError) as error:
        print(f"living-law runtime integration failure: {error}", file=sys.stderr)
        raise SystemExit(1) from error

    capsule_path: Path | None = None
    if args.capsule_output is not None:
        assert inquiry_runtime is not None
        try:
            capsule = inquiry_capsule(
                lean_root, module, inquiry_runtime, args.fuel, source, steps
            )
            args.capsule_output.write_text(
                json.dumps(capsule, ensure_ascii=False, indent=2, sort_keys=True)
                + "\n",
                encoding="utf-8",
            )
            capsule_path = args.capsule_output
        except (OSError, subprocess.CalledProcessError) as error:
            print(
                f"living-law runtime integration failure: unable to write "
                f"presentation capsule: {error}",
                file=sys.stderr,
            )
            raise SystemExit(1) from error

    print(f"module={module}")
    print(f"entry_kind={entry_kind}")
    print(f"entry={entry_name}")
    print(f"observed_ticks={args.fuel}")
    if args.fuel == 0:
        print("observation=exhausted (not terminal)")
    for step in steps:
        checks = (
            "occurrence,whole-ledger,installed-faces,next"
            if entry_kind == "micro"
            else "query,occurrence,resolution,answer,receipt,next,next-query"
        )
        print(
            f"step={step.index} kind={step.kind} "
            f"checks={checks}"
        )
    for diagnostic in diagnostics:
        print(f"lean-diagnostic={diagnostic}")
    if retained_probe is not None:
        print(f"probe={retained_probe}")
    if capsule_path is not None:
        print(f"capsule={capsule_path}")


if __name__ == "__main__":
    main()
