#!/usr/bin/env python3
"""Standalone runner for the NIST 2015 nominal-apparatus optimum replay (r0003).

Stages the SHA-256-pinned r0003 scripts and frozen inputs from their exported
repository locations into a temporary directory (leaving all tracked files
untouched), verifies every input digest, and executes:
  1. tests.py              (unit, symmetry, threshold, and local-optimality checks)
  2. replay.py             (primary Born-amplitude + pattern-search 16-corner replay)
  3. independent_replay.py (zero-shared-code 4x4 density-matrix + golden-section check)

Stdlib only (Python 3.9+), deterministic, offline. Works from both `git clone`
and a plain GitHub `.zip` archive download.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import sys
import tempfile

REPO_ROOT = Path(__file__).resolve().parents[4]

PINNED_CRITERION_FREEZE = {
    "path": "Verification/physics/stage10/independent-bell/nist-real/nominal-replay/criterion-r0003.md",
    "commit": "8e4b0643de1ceffbd5c39c72609358d240f3097c",
    "sha256": "2dd6d3e511da35415637edda8a164b1569c055a16ec7d25b99f262c5d86412d6",
}

STAGE_FILES = (
    (
        "instrument.json",
        "evidence/physics/bell-nist/nist-real/instrument.json",
        "4becca05d3a92bdd37d6218d83db64d80df5b4c605766056285d2bb32c0519c4",
    ),
    (
        "nominal-replay/criterion.md",
        "docs/source/physics/bell-nist/nist-real/nominal-replay/criterion.md",
        "64aa672be74be382693edfe17092a6b8244dfb26c971e484c891dc7bdfc283d5",
    ),
    (
        "nominal-replay/criterion-r0003.md",
        "evidence/first-release/ab/physics/stage10/independent-bell/nist-real/nominal-replay/criterion-r0003.md",
        "2dd6d3e511da35415637edda8a164b1569c055a16ec7d25b99f262c5d86412d6",
    ),
    (
        "nominal-replay/christensen-appendix-a.txt",
        "docs/source/physics/bell-nist/nist-real/nominal-replay/christensen-appendix-a.txt",
        "75dd07c2af8d81e42c410f04c8b8f32b7a884d4c23e8f505f377c44af70fdd5a",
    ),
    (
        "nominal-replay/shalm2015-channel-inputs.txt",
        "docs/source/physics/bell-nist/nist-real/nominal-replay/shalm2015-channel-inputs.txt",
        "17c5bc32515536634c451bf761f748ccd2e6c6002fa3949b58524e4cc1aeb3eb",
    ),
    (
        "nominal-replay/replay.py",
        "scripts/first-release/ab/physics/stage10/independent-bell/nist-real/nominal-replay/replay.py",
        "264bb4a516e6fadf2cf39114ff912cae43361de002ae3af62d4d93121ef3eac7",
    ),
    (
        "nominal-replay/independent_replay.py",
        "scripts/first-release/ab/physics/stage10/independent-bell/nist-real/nominal-replay/independent_replay.py",
        "05a597026b461f8c6525a082393d3d286a55dbcf3745c4d10144f1aeead0f21c",
    ),
    (
        "nominal-replay/tests.py",
        "scripts/first-release/ab/physics/stage10/independent-bell/nist-real/nominal-replay/tests.py",
        "30802cde28fb7bfcd1770a1abd90a5268d7feaba204e0b4ac9bbda0324dcc349",
    ),
)

ARCHIVED_REPLAY_JSON = (
    REPO_ROOT
    / "evidence/first-release/acceptance/scientific-20261005/nist-nominal-replay/replay-r0003.json"
)


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load module {name} from {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def verify_and_stage(stage_root: Path) -> Path:
    for staged_rel, repo_rel, expected_sha in STAGE_FILES:
        src = REPO_ROOT / repo_rel
        if not src.is_file():
            raise FileNotFoundError(f"Missing required repository file: {repo_rel}")
        actual_sha = sha256_file(src)
        if actual_sha != expected_sha:
            raise ValueError(
                f"SHA-256 mismatch for {repo_rel}: expected {expected_sha}, got {actual_sha}"
            )
        dst = stage_root / staged_rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
    return stage_root / "nominal-replay"


def verify_against_archived(fresh_replay_path: Path) -> None:
    if not ARCHIVED_REPLAY_JSON.is_file():
        return
    fresh = json.loads(fresh_replay_path.read_text(encoding="utf-8"))
    archived = json.loads(ARCHIVED_REPLAY_JSON.read_text(encoding="utf-8"))
    for key in ("schema", "verdict", "criterion_version", "bindings", "documented",
                "box_points", "band", "comparison", "diagnostics"):
        if fresh.get(key) != archived.get(key):
            raise AssertionError(f"Fresh replay output differs from archived receipt on '{key}'")
    print("archived receipt cross-check: EXACT MATCH on all deterministic fields")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--tests-only",
        action="store_true",
        help="Run only SHA-256 verification and unit/regression tests (~5 seconds).",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=None,
        help="Optional directory outside tracked paths to copy generated JSON receipts into.",
    )
    args = parser.parse_args()

    with tempfile.TemporaryDirectory(prefix="nist-r0003-") as tmp:
        work_dir = verify_and_stage(Path(tmp))
        print("SHA-256 check passed for all 8 pinned scripts and input files.")

        sys.path.insert(0, str(work_dir))
        try:
            replay_mod = load_module("replay", work_dir / "replay.py")
            ind_mod = load_module("independent_replay", work_dir / "independent_replay.py")
            replay_mod.find_repo_root = lambda _: "."
            replay_mod.criterion_freeze = lambda: dict(PINNED_CRITERION_FREEZE)
            ind_mod.criterion_freeze = lambda: dict(PINNED_CRITERION_FREEZE)

            print("\n=== [1/3] Running unit and physical sanity tests (tests.py) ===")
            tests_mod = load_module("tests", work_dir / "tests.py")
            rc = tests_mod.main()
            if rc != 0:
                return rc
            if args.tests_only:
                return 0

            print("\n=== [2/3] Running primary amplitude-path 16-corner replay (replay.py) ===")
            replay_mod.main()
            verify_against_archived(work_dir / "replay-r0003.json")

            print("\n=== [3/3] Running independent density-matrix check (independent_replay.py) ===")
            rc = ind_mod.main()
            if rc != 0:
                return rc

            if args.out_dir is not None:
                out_dir = args.out_dir.resolve()
                out_dir.mkdir(parents=True, exist_ok=True)
                for name in ("replay-r0003.json", "independent_replay-r0003.json"):
                    shutil.copy2(work_dir / name, out_dir / name)
                print(f"\nCopied generated JSON receipts to: {out_dir}")
        finally:
            if sys.path and sys.path[0] == str(work_dir):
                sys.path.pop(0)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
