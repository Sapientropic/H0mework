from collections import defaultdict
from pathlib import Path
import io
import json
import os
import shutil
import signal
import subprocess
import sys
import tarfile
import tempfile
import textwrap
import threading
import time
import unittest
from unittest.mock import patch

import ci_plan
from ci_plan import (LAYOUT, Layout, ReleaseStore, ancestors_within, build_part, closure, completed_setup_files,
                     coverage, estimate_costs, imports, make_plan, pack, prune_store, read_times, restore_choice,
                     save_archive, stage_number, stage_plan, sticky_assignment, unpack, update_times, write_layout)

# A synthetic project with ten-second modules spreads over several stages and shards.
SPLIT = Layout(window=25, workers=1, fill=1.0, shared_users=99, shared_chain=0)


def stage_builds(plan, dependencies):
    """Modules each part compiles: its targets' closure within its own stage."""
    members = defaultdict(set)
    for part in plan["parts"].values():
        members[part["stage"]] |= set(part["modules"])
    return {name: ancestors_within([t[1:] for t in part["targets"]], dependencies, members[part["stage"]])
            for name, part in plan["parts"].items()}


class PlanTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.sources = {
            "H0mework": "import H0mework.Papers.Demo\n",
            "H0mework.Foundation.Shared": "def shared := 1\n",
            "H0mework.Physics.Independent": "import H0mework.Foundation.Shared\n",
            "H0mework.Arithmetic.Independent": "import H0mework.Foundation.Shared\n",
            "H0mework.Chemistry.SourceParsing": "import H0mework.Foundation.Shared\n",
            "H0mework.Chemistry.LAlanineBandCall001.Check": "import H0mework.Chemistry.SourceParsing\n",
            "H0mework.Chemistry.LAlanineBandCall002.Check": "import H0mework.Chemistry.SourceParsing\n",
            "H0mework.Chemistry.LAlanineRefillRows.Block1": "import H0mework.Foundation.Shared\n",
            "H0mework.Chemistry.LAlanineRefillRows.Block2": "import H0mework.Chemistry.LAlanineRefillRows.Block1\n",
            "H0mework.Chemistry.LAlanineThermalLoad.Block1": "import H0mework.Chemistry.LAlanineBandCall001.Check\n",
            "H0mework.Papers.BaseOnly": "import H0mework.Foundation.Shared\n",
            "H0mework.Papers.Demo": "import H0mework.Physics.Independent\nimport H0mework.Chemistry.LAlanineBandCall001.Check\n",
            "H0mework.Versions.Y.Broken": "this historical source fails\n",
        }
        for name, source in self.sources.items():
            self.write_module(name, source)
        (self.root / "Lean/lean-toolchain").write_text("leanprover/lean4:v4.33.0\n")
        (self.root / "Lean/lake-manifest.json").write_text('{"packages": []}\n')
        (self.root / "evidence").mkdir()
        (self.root / "evidence/source.json").write_text('{"result": 1}\n')
        self.write_config()

    def write_module(self, name, text):
        path = self.root / "Lean" / (name.replace(".", "/") + ".lean")
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def write_config(self, *, package_options=None, library_options=None):
        ordinary = [n for n in self.sources if n not in {"H0mework.Chemistry.SourceParsing", "H0mework.Versions.Y.Broken"}]
        package = {"moreLeanArgs": ["--trust=0"], **(package_options or {})}
        package_text = "".join(f"{key} = {json.dumps(value)}\n" for key, value in package.items())
        library_text = "".join(f"{key} = {json.dumps(value)}\n" for key, value in (library_options or {}).items())
        (self.root / "Lean/lakefile.toml").write_text(
            'name = "H0mework"\ndefaultTargets = ["H0mework", "ResourceConsumers"]\n'
            f'{package_text}'
            '[[lean_lib]]\nname = "H0mework"\n'
            f'globs = {json.dumps(ordinary)}\nmoreLeanArgs = ["-DwarningAsError=true"]\n'
            '[[lean_lib]]\nname = "ResourceConsumers"\nroots = []\n'
            f'{library_text}'
            'globs = ["H0mework.Chemistry.SourceParsing"]\nneeds = ["ResourceInput"]\n'
            '[[lean_lib]]\nname = "Pinned"\nroots = []\n'
            'globs = ["H0mework.Versions.Y.Broken"]\n'
            '[[input_file]]\nname = "ResourceInput"\npath = "../evidence/source.json"\ntext = false\n'
        )

    def dependencies(self, plan):
        selected = {m for p in plan["parts"].values() for m in p["modules"]}
        return {n: [d for d in imports(self.sources[n]) if d in selected] for n in selected}

    def test_every_module_has_one_owner_and_each_import_is_earlier_or_rebuilt(self):
        for layout in (Layout(), SPLIT):
            plan = make_plan(self.root, layout)
            parts = {n: p for n, p in plan["parts"].items() if n != "complete"}
            owned = [m for p in parts.values() for m in p["modules"]]
            self.assertEqual(len(owned), len(set(owned)))
            self.assertEqual(set(owned), set(self.sources) - {"H0mework.Versions.Y.Broken"})
            dependencies = self.dependencies(plan)
            owner = {m: n for n, p in parts.items() for m in p["modules"]}
            builds = stage_builds(plan, dependencies)
            for name, part in parts.items():
                self.assertLessEqual(set(part["modules"]), builds[name], name)
                self.assertEqual(set(part["progress_modules"]), builds[name], name)
                needed = closure(builds[name], dependencies) - builds[name]
                self.assertEqual(set(part["upstream"]), {owner[m] for m in needed}, name)
                self.assertTrue(all(parts[u]["stage"] < part["stage"] for u in part["upstream"]), name)
            self.assertEqual(plan["parts"]["complete"]["upstream"], sorted(parts))
        # The split layout spreads the synthetic project over several stages and shares a module.
        self.assertGreater(len(plan["stages"]), 1)
        self.assertGreater(max(map(len, plan["stages"])), 1)
        self.assertGreater(sum("H0mework.Foundation.Shared" in b for b in builds.values()), 1)

    def test_plan_is_deterministic(self):
        self.assertEqual(make_plan(self.root, SPLIT), make_plan(self.root, SPLIT))

    def test_weak_lean_args_preserve_source_and_the_complete_plan(self):
        before = make_plan(self.root, SPLIT)
        source_bytes = {p: p.read_bytes() for p in (self.root / "Lean").rglob("*.lean")}
        for scope in ("package", "library", "both"):
            for args in ([], ["-DmaxHeartbeats=2000000"],
                         ["-DmaxHeartbeats=4000000", "-Dtrace.profiler=true"]):
                with self.subTest(scope=scope, args=args):
                    option = {"weakLeanArgs": args}
                    self.write_config(package_options=option if scope in {"package", "both"} else None,
                                      library_options=option if scope in {"library", "both"} else None)
                    self.assertEqual(make_plan(self.root, SPLIT), before)
        self.assertEqual({p: p.read_bytes() for p in source_bytes}, source_bytes)

    def assert_compiler_setting_invalidates_consumers(self, before, after, scope):
        self.assertEqual(after["compatibility"], before["compatibility"])
        self.assertEqual(after["assignment"], before["assignment"])
        self.assertNotEqual(after["selection"], before["selection"])
        dependencies = self.dependencies(before)
        for name, part in before["parts"].items():
            affected = name == "complete" or scope == "package" or (
                "H0mework.Chemistry.SourceParsing" in closure(part["modules"], dependencies))
            changed = part["fingerprint"] != after["parts"][name]["fingerprint"]
            self.assertEqual(changed, affected, name)

    def test_more_lean_args_overrides_still_invalidate_part_consumers(self):
        before = make_plan(self.root, SPLIT)
        for scope in ("package", "library"):
            with self.subTest(scope=scope):
                args = ["--trust=0"] if scope == "package" else []
                option = {"weakLeanArgs": ["-DmaxHeartbeats=2000000"],
                          "moreLeanArgs": [*args, "-DmaxHeartbeats=4000000"]}
                self.write_config(package_options=option if scope == "package" else None,
                                  library_options=option if scope == "library" else None)
                self.assert_compiler_setting_invalidates_consumers(before, make_plan(self.root, SPLIT), scope)

    def test_other_compiler_settings_are_not_weak_lean_args(self):
        before = make_plan(self.root, SPLIT)
        for key, value in (("leanOptions.maxHeartbeats", 2000000), ("moreLeancArgs", ["-O0"])):
            for scope in ("package", "library"):
                with self.subTest(key=key, scope=scope):
                    option = {key: value}
                    self.write_config(package_options=option if scope == "package" else None,
                                      library_options=option if scope == "library" else None)
                    self.assert_compiler_setting_invalidates_consumers(before, make_plan(self.root, SPLIT), scope)

    def test_selection_follows_content_and_ci_files_not_unrelated_files(self):
        def fingerprints(plan):
            return {p: v["fingerprint"] for p, v in plan["parts"].items() if p != "complete"}
        before = make_plan(self.root)
        (self.root / "evidence/notes.md").write_text("not a Lake input\n")
        self.assertEqual(make_plan(self.root)["selection"], before["selection"])
        workflow = self.root / ".github/workflows/ci.yml"
        workflow.parent.mkdir(parents=True)
        workflow.write_text("name: CI\n")
        revised_ci = make_plan(self.root)
        self.assertNotEqual(revised_ci["selection"], before["selection"])
        self.assertEqual(fingerprints(revised_ci), fingerprints(before))
        self.write_module("H0mework.Physics.Independent", self.sources["H0mework.Physics.Independent"] + "-- revised\n")
        self.assertNotEqual(make_plan(self.root)["selection"], revised_ci["selection"])

    def test_resource_change_invalidates_exactly_its_consumers(self):
        before = make_plan(self.root, SPLIT)
        (self.root / "evidence/source.json").write_text('{"result": 2}\n')
        after = make_plan(self.root, SPLIT)
        dependencies = self.dependencies(before)
        consumers = 0
        for name, part in before["parts"].items():
            if name == "complete":
                continue
            uses = "H0mework.Chemistry.SourceParsing" in closure(part["modules"], dependencies)
            consumers += uses
            changed = part["fingerprint"] != after["parts"][name]["fingerprint"]
            self.assertEqual(changed, uses, name)
        self.assertTrue(0 < consumers < len(before["parts"]) - 1)

    def test_real_import_header_ignores_comments_and_body_strings(self):
        source = '/- import H0mework.Wrong /- nested -/ -/\nmodule\npublic import H0mework.Foundation.Shared -- note\n'
        source += 'def example := "a /- quoted delimiter"\nimport H0mework.Wrong\n'
        self.assertEqual(imports(source), ["H0mework.Foundation.Shared"])

    def test_default_cannot_import_pinned_failure(self):
        self.write_module("H0mework", "import H0mework.Versions.Y.Broken\n")
        with self.assertRaisesRegex(ValueError, "non-default"):
            make_plan(self.root)

    def commit_layout(self, plan):
        (self.root / "tools").mkdir(exist_ok=True)
        write_layout(self.root / LAYOUT, plan["assignment"])

    def test_committed_layout_keeps_placements_and_adds_new_modules(self):
        before = make_plan(self.root, SPLIT)
        self.commit_layout(before)
        name = "H0mework.Papers.NewPaper"
        self.sources[name] = "import H0mework.Physics.Independent\n"
        self.write_module(name, self.sources[name])
        self.write_config()
        after = make_plan(self.root, SPLIT)
        self.assertEqual({m: s for m, s in after["assignment"].items() if m != name}, before["assignment"])
        self.assertEqual(after["placed"], 1)
        changed = {p for p in before["parts"] if p != "complete"
                   and before["parts"][p]["fingerprint"] != after["parts"][p]["fingerprint"]}
        self.assertLessEqual(changed, {after["assignment"][name]})

    def test_displaced_module_moves_after_its_new_import(self):
        before = make_plan(self.root, SPLIT)
        self.commit_layout(before)
        moved, stage = "H0mework.Physics.Independent", lambda plan, m: stage_number(plan["assignment"][m])
        dependencies = self.dependencies(before)
        later = sorted(m for m in dependencies if stage(before, m) > stage(before, moved)
                       and moved not in closure([m], dependencies))[0]
        self.write_module(moved, self.sources[moved] + f"import {later}\n")
        after = make_plan(self.root, SPLIT)
        self.assertGreaterEqual(stage(after, moved), stage(after, later))
        for part in after["parts"].values():
            self.assertTrue(all(after["parts"][u]["stage"] < part["stage"] for u in part["upstream"]))

    def checkout(self, name):
        path = self.root / "checkouts" / name
        shutil.copytree(self.root / "Lean", path / "Lean", ignore=shutil.ignore_patterns(".lake"))
        shutil.copytree(self.root / "evidence", path / "evidence")
        return path

    def lake_update(self):
        updated = subprocess.run(["lake", "update"], cwd=self.root / "Lean", capture_output=True, text=True)
        self.assertEqual(updated.returncode, 0, updated.stdout + updated.stderr)

    @unittest.skipUnless(shutil.which("lake") and shutil.which("zstd"), "Lean and zstd are required")
    def test_each_part_builds_from_its_declared_upstream_alone(self):
        self.lake_update()
        plan = make_plan(self.root, SPLIT)
        builds = stage_builds(plan, self.dependencies(plan))
        archives = {}
        for names in plan["stages"]:
            for name in names:
                part, checkout = plan["parts"][name], self.checkout(name)
                for upstream in part["upstream"]:
                    unpack(checkout, archives[upstream])
                started = time.time_ns()
                self.assertEqual(build_part(checkout, part), 0, name)
                lib = checkout / "Lean/.lake/build/lib/lean"
                fresh = {".".join(p.relative_to(lib).with_suffix("").parts) for p in lib.rglob("*.trace")
                         if p.stat().st_mtime_ns >= started}
                # Only this stage's modules compile; everything earlier came from upstream archives.
                self.assertTrue(set(part["modules"]) <= fresh <= builds[name], name)
                archives[name] = self.root / (name + ".tar.zst")
                pack(checkout, part["modules"], archives[name])
        final = self.checkout("complete")
        for archive in archives.values():
            unpack(final, archive)
        check = subprocess.run(["lake", "--no-build", "build"], cwd=final / "Lean", capture_output=True, text=True)
        self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
        # Lake's own module lists agree with the plan, and a part left out is reported.
        self.assertEqual(coverage(self.root, plan), (set(), set()))
        dropped = json.loads(json.dumps(plan))
        lost = dropped["parts"][plan["stages"][0][0]]["modules"].pop()
        self.assertEqual(coverage(self.root, dropped), ({lost}, set()))
        packet = final / "evidence/source.json"
        original = packet.read_bytes()
        packet.write_text('{"result": 2}\n')
        check = subprocess.run(["lake", "--no-build", "build"], cwd=final / "Lean", capture_output=True, text=True)
        self.assertEqual(check.returncode, 3, check.stdout + check.stderr)
        packet.write_bytes(original)
        (final / "Lean/.lake/build/lib/lean/H0mework/Physics/Independent.olean").unlink()
        check = subprocess.run(["lake", "--no-build", "build"], cwd=final / "Lean", capture_output=True, text=True)
        self.assertEqual(check.returncode, 3, check.stdout + check.stderr)

    @unittest.skipUnless(shutil.which("lake") and shutil.which("zstd"), "Lean and zstd are required")
    def test_progress_saved_at_a_deadline_resumes_in_another_checkout(self):
        slow = "H0mework.Physics.Slow"
        self.sources[slow] = "import H0mework.Physics.Independent\n#eval IO.sleep 15000\n"
        self.write_module(slow, self.sources[slow])
        self.write_config()
        self.lake_update()
        plan = make_plan(self.root)
        name = next(n for n, p in plan["parts"].items() if slow in p["modules"])
        earlier = [n for names in plan["stages"] for n in names if plan["parts"][n]["stage"] < plan["parts"][name]["stage"]]
        for n in earlier:
            self.assertEqual(build_part(self.root, plan["parts"][n]), 0, n)
        output = self.root / "outputs.txt"
        self.assertEqual(build_part(self.root, plan["parts"][name], output=output, deadline=time.time() + 6), 75)
        self.assertNotIn("built=0", output.read_text().splitlines())
        second = self.checkout("second")
        for n in [*earlier, name]:
            archive = self.root / "part.tar.zst"
            pack(self.root, plan["parts"][n]["modules"], archive)
            unpack(second, archive)
        for target, code in (("+H0mework.Physics.Independent", 0), ("+" + slow, 3)):
            check = subprocess.run(["lake", "--no-build", "build", target], cwd=second / "Lean", capture_output=True, text=True)
            self.assertEqual(check.returncode, code, check.stdout + check.stderr)
        output.unlink()
        self.assertEqual(build_part(second, plan["parts"][name], output=output), 0)
        self.assertIn("built=1", output.read_text().splitlines())

    @unittest.skipUnless(shutil.which("lake") and shutil.which("zstd"), "Lean and zstd are required")
    def test_shared_only_progress_survives_and_resumes_in_another_checkout(self):
        shared, owned = "H0mework.Physics.SharedProgress", "H0mework.Physics.OwnedProgress"
        self.sources[shared] = "theorem checkpointWitness : (1 : Nat) = 1 := rfl\n"
        self.sources[owned] = f"import {shared}\n#eval IO.sleep 15000\n"
        for name in (shared, owned):
            self.write_module(name, self.sources[name])
        self.write_config()
        self.lake_update()
        part = {"targets": ["+" + owned], "modules": [owned], "progress_modules": [shared, owned],
                "module_count": 1}
        output = self.root / "outputs.txt"
        self.assertEqual(build_part(self.root, part, output=output, deadline=time.time() + 6), 75)
        self.assertIn("built=1", output.read_text().splitlines())
        source_lib = self.root / "Lean/.lake/build/lib/lean"
        self.assertTrue((source_lib / "H0mework/Physics/SharedProgress.trace").exists())
        self.assertFalse((source_lib / "H0mework/Physics/OwnedProgress.trace").exists())

        plan = self.root / "plan.json"
        plan.write_text(json.dumps({"parts": {"s1-02": part}}))
        archive = self.root / "part.tar.zst"
        command = [sys.executable, str(Path(ci_plan.__file__).resolve()), "pack", "--root", str(self.root),
                   "--plan", str(plan), "--part", "s1-02", "--archive", str(archive)]
        # A full archive cannot publish another shard's modules.
        self.assertEqual(subprocess.run(command, capture_output=True).returncode, 0)
        ordinary = self.checkout("ordinary")
        unpack(ordinary, archive)
        self.assertFalse((ordinary / "Lean/.lake/build/lib/lean/H0mework/Physics/SharedProgress.olean").exists())

        self.assertEqual(subprocess.run([*command, "--checkpoint"], capture_output=True).returncode, 0)
        second = self.checkout("resume")
        unpack(second, archive)
        check = subprocess.run(["lake", "--no-build", "build", "+" + shared], cwd=second / "Lean", capture_output=True)
        self.assertEqual(check.returncode, 0, check.stdout + check.stderr)
        shared_file = second / "Lean/H0mework/Physics/SharedProgress.lean"
        shared_file.write_text(self.sources[shared] + "-- revised input\n")
        check = subprocess.run(["lake", "--no-build", "build", "+" + shared], cwd=second / "Lean", capture_output=True)
        self.assertEqual(check.returncode, 3, check.stdout + check.stderr)
        shared_file.write_text(self.sources[shared])

        trace = second / "Lean/.lake/build/lib/lean/H0mework/Physics/SharedProgress.trace"
        timestamp = trace.stat().st_mtime_ns
        output.unlink()
        self.assertEqual(build_part(second, part, output=output), 0)
        self.assertIn("built=1", output.read_text().splitlines())
        self.assertEqual(trace.stat().st_mtime_ns, timestamp)


class StagePlanTests(unittest.TestCase):
    def hub_and_families(self, hub_cost):
        dependencies = {"R": [], "H": ["R"], "J": [f"F{i}.b" for i in range(4)], "T": ["J"]}
        for i in range(4):
            dependencies[f"F{i}.a"], dependencies[f"F{i}.b"] = ["H"], [f"F{i}.a"]
        cost = {"R": 1, "H": hub_cost, "J": 1, "T": 5}
        cost.update({n: 10 for n in dependencies if n.startswith("F")})
        return dependencies, cost

    def test_light_shared_module_is_published_before_parallel_families(self):
        dependencies, cost = self.hub_and_families(hub_cost=1)
        layout = Layout(window=25, workers=1, fill=1.0, shared_users=3, shared_chain=5)
        stages = [[shard["build"] for shard in stage] for stage in stage_plan(dependencies, cost, layout)]
        self.assertEqual(stages[0], [{"R", "H"}])
        self.assertEqual(stages[1], [{f"F{i}.a", f"F{i}.b"} for i in range(4)])
        # The joiner needs every family, so it waits for the next stage with its consumer.
        self.assertEqual(stages[2], [{"J", "T"}])

    def test_costly_shared_module_is_rebuilt_by_each_family(self):
        dependencies, cost = self.hub_and_families(hub_cost=10)
        layout = Layout(window=40, workers=1, fill=1.0, shared_users=3, shared_chain=5)
        stages = [[shard["build"] for shard in stage] for stage in stage_plan(dependencies, cost, layout)]
        self.assertEqual(stages[0], [{"R"}])
        self.assertEqual(stages[1], [{"H", f"F{i}.a", f"F{i}.b"} for i in range(4)])
        self.assertEqual(stages[2], [{"J", "T"}])

    def test_new_module_waits_a_stage_rather_than_rebuilding_other_shards(self):
        dependencies, cost = self.hub_and_families(hub_cost=1)
        previous = {"R": "s1-01", "H": "s1-01", "J": "s3-01", "T": "s3-01"}
        previous.update({f"F{i}.{x}": f"s2-0{i + 1}" for i in range(4) for x in "ab"})
        dependencies.update({"K": ["F0.b"], "Joiner": [f"F{i}.b" for i in range(4)], "Big": ["F1.b"]})
        cost.update({"K": 1, "Joiner": 1, "Big": 10})
        layout = Layout(window=25, workers=1, fill=1.0)
        assignment = sticky_assignment(dependencies, cost, previous, layout)
        self.assertEqual({n: assignment[n] for n in previous}, previous)
        self.assertEqual(assignment["K"], "s2-01")         # beside its import, which has room
        self.assertEqual(stage_number(assignment["Joiner"]), 3)
        self.assertEqual(stage_number(assignment["Big"]), 3)  # its import's shard is full

    def test_estimates_prefer_measurement_then_nearest_namespace(self):
        times = {"A.B.x": 7.0, **{f"A.B.m{i}": float(i) for i in range(1, 6)}, **{f"C.n{i}": 100.0 for i in range(5)}}
        costs = estimate_costs(["A.B.x", "A.B.new", "A.Z.new", "D.new"], times)
        self.assertEqual(costs, {"A.B.x": 7.0, "A.B.new": 3.5, "A.Z.new": 3.5, "D.new": 7.0})

    def test_times_command_records_logged_seconds(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            log = root / "run.log"
            log.write_text("2026-10-01T00:00:00Z ✔ [3/9] Built H0mework.A.B (2.5s)\n"
                           "✔ [4/9] Built H0mework.A.C (320ms)\n✔ [5/9] Built Mathlib.X (9s)\n"
                           "ℹ [6/9] Replayed H0mework.A.D\n")
            table = root / "ci_times.tsv"
            table.write_text("1\tH0mework.A.B\n5\tH0mework.Z\n")
            self.assertEqual(update_times(table, [log], 2.0), 2)
            self.assertEqual(read_times(table), {"H0mework.A.B": 5.0, "H0mework.A.C": 0.6, "H0mework.Z": 5.0})


class BuildTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "Lean").mkdir()
        self.output = self.root / "outputs.txt"
        self.part = {"targets": ["+H0mework.Done"], "modules": ["H0mework.Done", "H0mework.Pending"],
                     "module_count": 2}

    def lake(self, body, probe=3):
        # Stand-in Lake: the probe exits with `probe`; a build finishes one module,
        # then runs `body`.
        bin_dir = self.root / "bin"
        bin_dir.mkdir(exist_ok=True)
        script = bin_dir / "lake"
        script.write_text(f"#!{sys.executable}\n" + textwrap.dedent(f"""
            import pathlib, signal, subprocess, sys
            signal.signal(signal.SIGINT, signal.SIG_DFL)
            if sys.argv[1] == "--no-build":
                sys.exit({probe})
            trace = pathlib.Path(".lake/build/lib/lean/H0mework/Done.trace")
            trace.parent.mkdir(parents=True, exist_ok=True)
            trace.write_text("built")
        """) + textwrap.dedent(body))
        script.chmod(0o755)
        return patch.dict(os.environ, {"PATH": f"{bin_dir}{os.pathsep}{os.environ['PATH']}"})

    def outputs(self):
        return dict(line.split("=", 1) for line in self.output.read_text().splitlines())

    def assert_gone(self, pid):
        end = time.monotonic() + 5
        while time.monotonic() < end:
            try:
                os.kill(pid, 0)
            except ProcessLookupError:
                return
            time.sleep(0.05)
        self.fail(f"process {pid} survived the stop")

    def test_status_separates_current_complete_failed_and_probe_errors(self):
        cases = [(0, "sys.exit(0)", 0, "true", "complete", "0"), (3, "sys.exit(0)", 0, "false", "complete", "1"),
                 (3, "sys.exit(1)", 1, "false", "failed", "1"), (2, "sys.exit(0)", 2, "false", "failed", "0")]
        for probe, body, code, current, status, built in cases:
            with self.subTest(probe=probe, body=body), self.lake(body, probe):
                self.output.unlink(missing_ok=True)
                self.assertEqual(build_part(self.root, self.part, output=self.output), code)
                self.assertEqual(self.outputs(), {"started": "true", "current": current, "status": status, "built": built})

    def test_deadline_stops_lake_and_its_children_and_keeps_progress(self):
        child = """
            child = subprocess.Popen([sys.executable, "-c",
                "import signal, time; signal.signal(signal.SIGINT, signal.SIG_DFL); time.sleep(60)"])
            pathlib.Path("child.pid").write_text(str(child.pid))
            child.wait()
        """
        with self.lake(child):
            began = time.monotonic()
            code = build_part(self.root, self.part, output=self.output, deadline=time.time() + 1.5)
        self.assertEqual(code, 75)
        self.assertLess(time.monotonic() - began, 20)
        self.assertEqual((self.outputs()["status"], self.outputs()["built"]), ("incomplete", "1"))
        self.assert_gone(int((self.root / "Lean/child.pid").read_text()))

    def test_same_stage_copy_counts_as_progress_at_deadline_and_cancellation(self):
        self.part.update(targets=["+H0mework.Pending"], modules=["H0mework.Pending"], module_count=1,
                         progress_modules=["H0mework.Done", "H0mework.Pending"])
        for stop in ("deadline", "cancelled"):
            with self.subTest(stop=stop), self.lake("import time\ntime.sleep(60)\n"):
                self.output.unlink(missing_ok=True)
                if stop == "deadline":
                    code = build_part(self.root, self.part, output=self.output, deadline=time.time() + 1.5)
                    self.assertEqual(code, 75)
                else:
                    timer = threading.Timer(1.0, os.kill, (os.getpid(), signal.SIGTERM))
                    timer.start()
                    try:
                        code = build_part(self.root, self.part, output=self.output)
                    finally:
                        timer.cancel()
                    self.assertEqual(code, 130)
                self.assertEqual(self.outputs()["built"], "1")

    def test_module_outside_the_build_scope_does_not_request_continuation(self):
        self.part.update(targets=["+H0mework.Pending"], modules=["H0mework.Pending"], module_count=1,
                         progress_modules=["H0mework.Pending"])
        with self.lake("import time\ntime.sleep(60)\n"):
            code = build_part(self.root, self.part, output=self.output, deadline=time.time() + 1.5)
        self.assertEqual(code, 75)
        self.assertEqual((self.outputs()["status"], self.outputs()["built"]), ("incomplete", "0"))

    def test_cancellation_signal_stops_the_build(self):
        with self.lake("import time\ntime.sleep(60)\n"):
            timer = threading.Timer(1.0, os.kill, (os.getpid(), signal.SIGTERM))
            timer.start()
            try:
                code = build_part(self.root, self.part, output=self.output)
            finally:
                timer.cancel()
        self.assertEqual(code, 130)
        self.assertEqual(self.outputs()["status"], "cancelled")
        self.assertIs(signal.getsignal(signal.SIGTERM), signal.SIG_DFL)


@unittest.skipUnless(shutil.which("zstd"), "zstd is needed for artifact transport")
class ArtifactTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.build = self.root / "Lean/.lake/build"

    def file(self, relative, data=b"checked module"):
        path = self.build / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
        return path

    def test_round_trip_keeps_owned_artifacts_and_excludes_setup_and_other_parts(self):
        self.file("lib/lean/H0mework/Example.olean")
        self.file("lib/lean/H0mework/Example.trace")
        self.file("ir/H0mework/Example.c")
        self.file("ir/H0mework/Example.setup.json", b"temporary absolute paths")
        self.file("lib/lean/H0mework/Other.olean")
        archive = self.root / "part.tar.zst"
        pack(self.root, ["H0mework.Example"], archive)
        destination = self.root / "destination"
        unpack(destination, archive)
        restored = destination / "Lean/.lake/build"
        self.assertEqual((restored / "lib/lean/H0mework/Example.olean").read_bytes(), b"checked module")
        self.assertFalse((restored / "ir/H0mework/Example.setup.json").exists())
        self.assertFalse((restored / "lib/lean/H0mework/Other.olean").exists())

    def test_archive_traversal_is_rejected(self):
        raw = io.BytesIO()
        with tarfile.open(fileobj=raw, mode="w") as tar:
            entry = tarfile.TarInfo("../../escape")
            entry.size = 3
            tar.addfile(entry, io.BytesIO(b"bad"))
        archive = self.root / "unsafe.tar.zst"
        archive.write_bytes(subprocess.check_output(["zstd", "-q", "-c"], input=raw.getvalue()))
        with self.assertRaisesRegex(ValueError, "Invalid artifact"):
            unpack(self.root, archive)
        self.assertFalse((self.root / "escape").exists())

    def test_janitor_waits_for_compilation_trace(self):
        setup = self.file("ir/H0mework/Example.setup.json")
        trace = self.file("lib/lean/H0mework/Example.trace")
        os.utime(trace, ns=(10, 10))
        os.utime(setup, ns=(20, 20))
        self.assertEqual(completed_setup_files(self.build), 0)
        self.assertTrue(setup.exists())
        os.utime(trace, ns=(30, 30))
        self.assertEqual(completed_setup_files(self.build), 1)
        self.assertFalse(setup.exists())


class FakeStore(ReleaseStore):
    def __init__(self):
        super().__init__("owner/repo", "token")
        self.data, self.clock = {}, 0

    def open(self, create=False):
        if self.release_id is None and create:
            self.release_id = 1
        if self.release_id is not None and self.assets is None:
            self.assets = {}
        return self.release_id is not None

    def download(self, asset, output):
        output.write(self.data[asset["id"]])

    def upload(self, name, source):
        self.clock += 1
        self.data[name] = source.read_bytes()
        self.assets[name] = {"id": name, "name": name, "created_at": f"2026-10-01T00:00:{self.clock:02d}Z"}

    def api(self, method, path, body=None):
        assert method == "DELETE"
        del self.data[path.rsplit("/", 1)[1]]


class StoreTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def file(self, name, data):
        path = self.root / name
        path.write_bytes(data)
        return path

    def test_restore_prefers_exact_then_newest_progress_then_newest_version(self):
        key, prefix = "L-v1-c-s1-01-new", "L-v1-c-s1-01-"
        entries = {f"{key}-7-1.tar.zst": "2", f"{key}-8-1.tar.zst": "3", f"{prefix}old.tar.zst": "4",
                   "L-v1-c-s1-011-other.tar.zst": "9"}
        self.assertEqual(restore_choice(entries, key, prefix), (f"{key}-8-1.tar.zst", False))
        entries[key + ".tar.zst"] = "1"
        self.assertEqual(restore_choice(entries, key, prefix), (key + ".tar.zst", True))
        older = {f"{prefix}old.tar.zst": "4", f"{prefix}older.tar.zst": "1"}
        self.assertEqual(restore_choice(older, key, prefix), (f"{prefix}old.tar.zst", False))
        self.assertEqual(restore_choice({}, key, prefix), (None, False))

    def test_split_archive_round_trips_and_counts_once(self):
        store, data = FakeStore(), bytes(range(256)) * 3
        with patch("ci_plan.ASSET_LIMIT", 100):
            store.put("big.tar.zst", self.file("big", data))
        self.assertEqual(sorted(store.assets), [*(f"big.tar.zst.{i:03d}" for i in range(8)), "big.tar.zst.parts"])
        self.assertEqual(list(store.entries()), ["big.tar.zst"])
        self.assertTrue(store.fetch("big.tar.zst", self.root / "restored"))
        self.assertEqual((self.root / "restored").read_bytes(), data)
        store.remove(["big.tar.zst"])
        self.assertEqual(store.assets, {})

    def test_listing_taken_once_serves_later_jobs(self):
        store = FakeStore()
        store.put("k.tar.zst", self.file("part", b"outputs"))
        store.dump(self.root / "store.json")
        later = ReleaseStore("owner/repo", "token")
        later.load(self.root / "store.json")
        # No request is needed to list the store again.
        with patch.object(ReleaseStore, "pages", side_effect=AssertionError("listed again")):
            self.assertEqual(list(later.entries()), ["k.tar.zst"])

    def test_progress_and_full_archives_supersede_older_progress(self):
        store, archive = FakeStore(), self.file("part", b"outputs")
        save_archive(store, "k", archive, "1-1")
        save_archive(store, "k", archive, "2-1")
        self.assertEqual(list(store.entries()), ["k-2-1.tar.zst"])
        save_archive(store, "k", archive)
        self.assertEqual(list(store.entries()), ["k.tar.zst"])

    def test_prune_keeps_current_archives_and_waits_until_all_are_stored(self):
        store, archive = FakeStore(), self.file("part", b"outputs")
        tag = ci_plan.platform_tag()
        current = {f"{tag}-{ci_plan.CACHE_VERSION}-c-s1-01-new.tar.zst", f"{tag}-lean-selection-new.json"}
        stale = [f"{tag}-{ci_plan.CACHE_VERSION}-c-s1-01-old.tar.zst", f"{tag}-lean-selection-old.json"]
        for name in [*stale, "unrelated.bin", sorted(current)[0]]:
            store.put(name, archive)
        self.assertEqual(prune_store(store, current), [])  # the seal is not stored yet
        store.put(sorted(current)[1], archive)
        self.assertEqual(prune_store(store, current), sorted(stale))
        self.assertEqual(set(store.entries()), current | {"unrelated.bin"})


if __name__ == "__main__":
    unittest.main()
