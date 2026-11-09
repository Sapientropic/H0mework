#!/usr/bin/env python3
"""Generate the Proposition-series dependency/role/axiom inventory.

The default report is derived from `LivingLawActive.roots` and the live import
graph.  It is intentionally not a committed architecture ledger: roles are
search hints, while authority still comes from the named root facades and
their checked Lean declarations.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
import tomllib
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


IMPORT_RE = re.compile(r"^\s*import\s+([^\s]+)\s*$", re.MULTILINE)
PROPOSITION_RE = re.compile(r"^SaturationMonoid\.Proposition([0-9]+)(?:[A-Za-z_].*)?$")
DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:noncomputable|protected)\s+)*"
    r"(private\s+|local\s+)?"
    r"(theorem|def|abbrev|structure|inductive|class|opaque|axiom)"
    r"(?:\s+|$)(.*)$"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([^\s]+)\s*$")
SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+[^\s]+)?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+[^\s]+)?\s*$")
NAME_RE = re.compile(r"^([^\s(:{\[=]+)")


@dataclass(frozen=True)
class Declaration:
    name: str
    kind: str
    role_hints: tuple[str, ...]


def module_name(lean_root: Path, source: Path) -> str:
    return ".".join(source.relative_to(lean_root).with_suffix("").parts)


def collect_modules(lean_root: Path) -> tuple[dict[str, Path], dict[str, set[str]]]:
    modules: dict[str, Path] = {}
    imports: dict[str, set[str]] = {}
    for source in lean_root.rglob("*.lean"):
        relative = source.relative_to(lean_root)
        if relative.parts[0] in {".lake", "scratch"}:
            continue
        module = module_name(lean_root, source)
        modules[module] = source
        imports[module] = set(IMPORT_RE.findall(source.read_text(encoding="utf-8")))
    return modules, imports


def closure(root: str, imports: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    pending = [root]
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        pending.extend(imports.get(module, ()))
    return seen


def shortest_import_path(
    root: str, target: str, imports: dict[str, set[str]]
) -> list[str] | None:
    """Return one deterministic shortest root-to-target import path."""
    pending = deque([(root, [root])])
    seen = {root}
    while pending:
        module, path = pending.popleft()
        if module == target:
            return path
        for dependency in sorted(imports.get(module, ())):
            if dependency in seen:
                continue
            seen.add(dependency)
            pending.append((dependency, [*path, dependency]))
    return None


def reverse_graph(imports: dict[str, set[str]]) -> dict[str, set[str]]:
    reverse: dict[str, set[str]] = defaultdict(set)
    for importer, dependencies in imports.items():
        for dependency in dependencies:
            reverse[dependency].add(importer)
    return reverse


def reverse_closure(module: str, reverse: dict[str, set[str]]) -> set[str]:
    seen: set[str] = set()
    pending = list(reverse.get(module, ()))
    while pending:
        importer = pending.pop()
        if importer in seen:
            continue
        seen.add(importer)
        pending.extend(reverse.get(importer, ()))
    return seen


def role_hints(name: str, kind: str) -> tuple[str, ...]:
    lowered = name.lower()
    roles: set[str] = set()
    if kind in {"structure", "inductive", "class"} or re.search(
        r"producer|process|generated|generate|compile|actual|update|source|write",
        lowered,
    ):
        roles.add("producer-candidate")
    if re.search(
        r"transport|equiv|commut|natural|preserv|lift|pullback|pushforward|morphism",
        lowered,
    ):
        roles.add("transporter")
    if re.search(
        r"readout|projection|observe|trace|energy|fixed|_eq|_iff|to[a-z]",
        lowered,
    ):
        roles.add("readout")
    if re.search(
        r"impossible|no_?go|reject|obstruction|noninject|counterexample|false|cannot|forbid",
        lowered,
    ):
        roles.add("diagnostic")
    if not roles:
        roles.add("unclassified")
    return tuple(sorted(roles))


def strip_lean_comments(text: str) -> str:
    """Remove nested Lean comments while preserving source line boundaries."""
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    escaped = False
    while index < len(text):
        current = text[index]
        following = text[index + 1] if index + 1 < len(text) else ""
        if block_depth:
            if current == "/" and following == "-":
                block_depth += 1
                output.extend((" ", " "))
                index += 2
                continue
            if current == "-" and following == "/":
                block_depth -= 1
                output.extend((" ", " "))
                index += 2
                continue
            output.append("\n" if current == "\n" else " ")
            index += 1
            continue
        if in_string:
            output.append(current)
            if escaped:
                escaped = False
            elif current == "\\":
                escaped = True
            elif current == '"':
                in_string = False
            index += 1
            continue
        if current == '"':
            in_string = True
            output.append(current)
            index += 1
            continue
        if current == "/" and following == "-":
            block_depth = 1
            output.extend((" ", " "))
            index += 2
            continue
        if current == "-" and following == "-":
            while index < len(text) and text[index] != "\n":
                output.append(" ")
                index += 1
            continue
        output.append(current)
        index += 1
    return "".join(output)


def public_declarations(source: Path) -> list[Declaration]:
    lines = strip_lean_comments(source.read_text(encoding="utf-8")).splitlines()
    namespace: list[str] = []
    blocks: list[tuple[str, int]] = []
    declarations: list[Declaration] = []
    index = 0
    while index < len(lines):
        line = lines[index]
        namespace_match = NAMESPACE_RE.match(line)
        if namespace_match:
            parts = namespace_match.group(1).split(".")
            namespace.extend(parts)
            blocks.append(("namespace", len(parts)))
            index += 1
            continue
        if SECTION_RE.match(line):
            blocks.append(("section", 0))
            index += 1
            continue
        if END_RE.match(line):
            if blocks:
                kind, count = blocks.pop()
                if kind == "namespace" and count:
                    del namespace[-count:]
            index += 1
            continue
        declaration_match = DECL_RE.match(line)
        if not declaration_match:
            index += 1
            continue
        privacy, kind, remainder = declaration_match.groups()
        if privacy:
            index += 1
            continue
        candidate = remainder.strip()
        lookahead = index + 1
        while not candidate and lookahead < len(lines):
            candidate = lines[lookahead].strip()
            lookahead += 1
        name_match = NAME_RE.match(candidate)
        if name_match:
            short_name = name_match.group(1)
            if short_name.startswith("_root_."):
                qualified = short_name.removeprefix("_root_.")
            else:
                qualified = ".".join((*namespace, short_name))
            declarations.append(
                Declaration(qualified, kind, role_hints(short_name, kind))
            )
        index += 1
    return declarations


def root_labels(modules: list[str]) -> list[tuple[str, str]]:
    """Give lake-owned roots deterministic presentation-only labels."""
    short_names = [module.rsplit(".", 1)[-1] for module in modules]
    duplicates = {
        name for name in short_names if short_names.count(name) > 1
    }
    return [
        (module if short in duplicates else short, module)
        for module, short in zip(modules, short_names, strict=True)
    ]


def active_lake_roots(lean_root: Path) -> list[tuple[str, str]]:
    """Read the sole default authority graph from `LivingLawActive`."""
    with (lean_root / "lakefile.toml").open("rb") as lakefile:
        configuration = tomllib.load(lakefile)
    for library in configuration.get("lean_lib", []):
        if library.get("name") == "LivingLawActive":
            modules = library.get("roots")
            if not isinstance(modules, list) or not all(
                isinstance(module, str) for module in modules
            ):
                raise ValueError(
                    "LivingLawActive.roots must be an explicit string array"
                )
            if not modules:
                raise ValueError("LivingLawActive.roots must not be empty")
            return root_labels(modules)
    raise ValueError("lakefile.toml has no LivingLawActive lean_lib")


def parse_roots(
    values: list[str], lean_root: Path
) -> list[tuple[str, str]]:
    if not values:
        return active_lake_roots(lean_root)
    roots: list[tuple[str, str]] = []
    for value in values:
        if "=" in value:
            label, module = value.split("=", 1)
        else:
            module = value
            label = module.rsplit(".", 1)[-1]
        roots.append((label, module))
    return roots


def run_axiom_audit(
    lean_root: Path,
    roots: list[tuple[str, str]],
    declarations: Iterable[Declaration],
    build: bool,
) -> dict[str, list[str]]:
    root_modules = list(dict.fromkeys(module for _, module in roots))
    if build:
        subprocess.run(
            ["lake", "build", *root_modules], cwd=lean_root, check=True,
            stdout=sys.stderr, stderr=sys.stderr,
        )
    declarations = list(dict.fromkeys(declaration.name for declaration in declarations))
    with tempfile.NamedTemporaryFile(
        "w", suffix=".lean", prefix="proposition-axioms-", dir=lean_root / "scratch",
        encoding="utf-8", delete=False
    ) as audit:
        audit_path = Path(audit.name)
        for module in root_modules:
            audit.write(f"import {module}\n")
        audit.write("\n")
        for declaration in declarations:
            audit.write(f"#print axioms {declaration}\n")
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(audit_path.relative_to(lean_root))],
            cwd=lean_root,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    finally:
        audit_path.unlink(missing_ok=True)
    normalized = " ".join(result.stdout.split())
    dependencies: dict[str, list[str]] = {}
    for name in declarations:
        escaped = re.escape(name)
        empty = re.search(
            rf"'{escaped}' does not depend on any axioms", normalized
        )
        if empty:
            dependencies[name] = []
            continue
        populated = re.search(
            rf"'{escaped}' depends on axioms: \[([^\]]*)\]", normalized
        )
        if populated:
            dependencies[name] = [
                item.strip() for item in populated.group(1).split(",") if item.strip()
            ]
    missing = sorted(set(declarations) - dependencies.keys())
    if result.returncode != 0 or missing:
        excerpt = result.stdout[-4000:]
        raise RuntimeError(
            "Lean axiom audit did not cover every declaration. "
            f"missing={missing[:20]}\n{excerpt}"
        )
    return dependencies


def git_revision(repo_root: Path) -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"], cwd=repo_root, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL
    )
    return result.stdout.strip() if result.returncode == 0 else "unknown"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--root", action="append", default=[], metavar="LABEL=MODULE",
        help=("authority facade/root; repeat to replace the "
              "LivingLawActive.roots defaults"),
    )
    parser.add_argument("--format", choices=("json", "tsv"), default="tsv")
    parser.add_argument(
        "--with-axioms", action="store_true",
        help="build the selected roots and run #print axioms for reachable P declarations",
    )
    parser.add_argument(
        "--no-build", action="store_true",
        help="with --with-axioms, reuse existing oleans instead of running lake build",
    )
    parser.add_argument(
        "--reachable-only", action="store_true",
        help="omit P modules not reachable from a selected root",
    )
    parser.add_argument(
        "--assert-none-reachable", action="store_true",
        help=("fail when any Proposition module is reachable from the "
              "selected roots"),
    )
    args = parser.parse_args()

    lean_root = Path(__file__).resolve().parents[1]
    repo_root = lean_root.parent
    try:
        roots = parse_roots(args.root, lean_root)
    except (OSError, UnicodeError, tomllib.TOMLDecodeError, ValueError) as error:
        parser.error(str(error))
    modules, imports = collect_modules(lean_root)
    unknown_roots = [module for _, module in roots if module not in modules]
    if unknown_roots:
        parser.error(f"unknown local root modules: {', '.join(unknown_roots)}")
    unclassified_propositions = sorted(
        module for module in modules
        if module.startswith("SaturationMonoid.Proposition")
        and PROPOSITION_RE.fullmatch(module) is None
    )
    if unclassified_propositions:
        parser.error(
            "unclassified Proposition modules: "
            + ", ".join(unclassified_propositions)
        )

    root_closures = {label: closure(module, imports) for label, module in roots}
    reverse = reverse_graph(imports)
    propositions: list[dict[str, object]] = []
    all_reachable_declarations: list[Declaration] = []

    for module, source in modules.items():
        number_match = PROPOSITION_RE.match(module)
        if not number_match:
            continue
        reachable_from = sorted(
            label for label, reached in root_closures.items() if module in reached
        )
        if args.reachable_only and not reachable_from:
            continue
        declarations = public_declarations(source)
        proposition_imports = sorted(imports.get(module, ()))
        compatibility_only = not declarations and len(proposition_imports) == 1
        if reachable_from:
            all_reachable_declarations.extend(declarations)
        role_set = {
            role for declaration in declarations for role in declaration.role_hints
        }
        if len(role_set) > 1:
            role_set.discard("unclassified")
        roles = sorted(role_set)
        if compatibility_only:
            roles = ["compatibility-import"]
        declared_axioms = [
            declaration.name for declaration in declarations if declaration.kind == "axiom"
        ]
        import_paths = {
            label: path
            for label, root_module in roots
            if (path := shortest_import_path(root_module, module, imports)) is not None
        }
        root_entrypoints = sorted(
            f"{label}:{path[1] if len(path) > 1 else path[0]}"
            for label, path in import_paths.items()
        )
        propositions.append(
            {
                "number": int(number_match.group(1)),
                "module": module,
                "path": str(source.relative_to(repo_root)),
                "lines": sum(1 for _ in source.open(encoding="utf-8")),
                "reachable_from": reachable_from,
                "root_entrypoints": root_entrypoints,
                "import_paths": import_paths,
                "direct_fanout": len(reverse.get(module, ())),
                "transitive_fanout": len(reverse_closure(module, reverse)),
                "role_hints": roles or ["unclassified"],
                "compatibility_only": compatibility_only,
                "imports": proposition_imports,
                "declared_axioms": declared_axioms,
                "declarations": [
                    {
                        "name": declaration.name,
                        "kind": declaration.kind,
                        "role_hints": list(declaration.role_hints),
                    }
                    for declaration in declarations
                ],
            }
        )

    reachable_propositions = [
        item for item in propositions if item["reachable_from"]
    ]
    if args.assert_none_reachable and reachable_propositions:
        modules = ", ".join(
            str(item["module"]) for item in reachable_propositions[:12]
        )
        suffix = "" if len(reachable_propositions) <= 12 else ", ..."
        raise SystemExit(
            "selected roots reach Proposition modules: "
            f"count={len(reachable_propositions)}; {modules}{suffix}"
        )

    axiom_dependencies: dict[str, list[str]] = {}
    if args.with_axioms:
        axiom_dependencies = run_axiom_audit(
            lean_root, roots, all_reachable_declarations, not args.no_build
        )
        for proposition in propositions:
            dependencies = {
                declaration["name"]: axiom_dependencies[declaration["name"]]
                for declaration in proposition["declarations"]
                if declaration["name"] in axiom_dependencies
            }
            proposition["axiom_dependencies"] = dependencies
            proposition["axiom_union"] = sorted(
                {axiom for values in dependencies.values() for axiom in values}
            )
    else:
        for proposition in propositions:
            proposition["axiom_dependencies"] = None
            proposition["axiom_union"] = None

    propositions.sort(
        key=lambda item: (
            not bool(item["reachable_from"]),
            -int(item["transitive_fanout"]),
            int(item["number"]),
        )
    )
    report = {
        "revision": git_revision(repo_root),
        "roots": [{"label": label, "module": module} for label, module in roots],
        "proposition_count": len(propositions),
        "reachable_count": len(reachable_propositions),
        "role_warning": "role_hints are lexical routing hints, never theorem authority",
        "axioms_audited": args.with_axioms,
        "propositions": propositions,
    }

    if args.format == "json":
        print(json.dumps(report, ensure_ascii=False, indent=2))
        return
    print(
        "number\tmodule\tlines\treachable_from\tdirect_fanout\t"
        "transitive_fanout\troot_entrypoints\trole_hints\t"
        "compatibility_only\taxiom_union"
    )
    for item in propositions:
        axiom_union = item["axiom_union"]
        print(
            f"{item['number']}\t{item['module']}\t{item['lines']}\t"
            f"{','.join(item['reachable_from']) or '-'}\t"
            f"{item['direct_fanout']}\t{item['transitive_fanout']}\t"
            f"{','.join(item['root_entrypoints']) or '-'}\t"
            f"{','.join(item['role_hints'])}\t{str(item['compatibility_only']).lower()}\t"
            f"{','.join(axiom_union) if axiom_union is not None else 'not-audited'}"
        )


if __name__ == "__main__":
    main()
