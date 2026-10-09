#!/usr/bin/env python3
"""Authenticate and losslessly compare this exact fifteen-name re-emission set.

Reuses the already signed complete-parts comparator. No mathematical compilation,
raw artifact copying, private suffix matching or paid-frontier bypass is used.
"""
from __future__ import annotations

import argparse
from collections import defaultdict
import hashlib
import json
from pathlib import Path
import runpy
import sys


ROOT = Path(__file__).resolve().parent
MANIFEST = ROOT / "paid-lazy-reemissions-signed-baselines.json"
MANIFEST_SHA = "b1107e14eabfb05f925d5a6624f04373b765f544d881486e5fdb407fdc6ac513"
COMPARATOR_SHA = "0ebd3bd19c9da886374995e7e5a0b78d6e50204b4fc86943fb196a6bd671370f"
ANCHOR_SHA = "78f8a49c0b64175008615eab77549aa12dbe2a815aab31d7e711da96e6f42ca0"
EXPECTED_NAMES = frozenset({f"CPS1LiveEditing.RawSupply.species.eq_{i}" for i in range(1, 11)} | {
    "CPS1BiologicalUpdate.BiologicalDisposition.localUpdate.congr_simp",
    "CPS1BiologicalUpdate.RenewedBiosynthesis.mk.congr_simp",
    "CPS1LiveEditing.GenomicDisposition.rejected.congr_simp",
    "CPS1LiveEditing.TranslationDisposition.decodingRejected.congr_simp",
    "_private.CPS1LiveEditing.Translation.0.CPS1LiveEditing.makeTranslation.congr_simp",
})


def require(condition, message, **context):
    if not condition:
        raise ValueError(message + (" " + json.dumps(context, ensure_ascii=False, sort_keys=True) if context else ""))


def read_bound(binding):
    path = Path(binding["path"])
    raw = path.read_bytes()
    require(len(raw) == binding["bytes"] and hashlib.sha256(raw).hexdigest() == binding["sha256"],
            "SIGNED_BINDING_MISMATCH", binding=binding)
    return raw


def bound_in(binding, references):
    return any(all(reference.get(key) == binding.get(key) for key in ("path", "sha256", "bytes"))
               for reference in references)


def certified(binding):
    record = json.loads(read_bound(binding))
    require(record.get("verdict") == "certified", "UNCERTIFIED_RECEIPT", path=binding["path"])
    return record


def load_trust_chain():
    raw = MANIFEST.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == MANIFEST_SHA, "MANIFEST_SHA_MISMATCH")
    manifest = json.loads(raw)
    require(manifest["schema"] == "CPS1-native-registration-exact-paid-lazy-baselines/v1", "MANIFEST_SCHEMA")
    require(set(manifest["exact_rechecked_names"]) == EXPECTED_NAMES and len(manifest["exact_rechecked_names"]) == 15,
            "MANIFEST_EXACT_NAME_SET")
    require(manifest["signed_parent_anchor"]["sha256"] == ANCHOR_SHA, "WRONG_TRUST_ANCHOR")
    parent = certified(manifest["signed_parent_anchor"])
    for link in manifest["current_receipt_chain"]:
        require(link["field"] == "signed_parent_receipts" and bound_in(link["receipt"], parent[link["field"]]),
                "CURRENT_RECEIPT_CHAIN_NOT_BOUND")
        parent = certified(link["receipt"])
    prior_binding = manifest["signed_prior_baseline_manifest"]
    comparator_binding = manifest["signed_reused_comparator"]
    require(bound_in(prior_binding, [parent["migration"]["baseline_manifest"]]) and
            bound_in(comparator_binding, [parent["migration"]["comparator"]]), "PRIOR_CERTIFIER_NOT_SIGNED")
    require(comparator_binding["sha256"] == COMPARATOR_SHA, "REUSED_COMPARATOR_SHA_CHANGED")
    read_bound(comparator_binding)
    prior = json.loads(read_bound(prior_binding))
    require(bound_in(manifest["signed_same_event_receipt"], [group["signed_receipt"] for group in prior["groups"]]),
            "SAME_EVENT_BASELINE_NOT_PRIOR_BOUND")
    same_event = certified(manifest["signed_same_event_receipt"])
    declarations = [name for group in manifest["groups"] for name in group["exact_declarations"]]
    require(set(declarations) == EXPECTED_NAMES and len(declarations) == 15, "GROUP_COVERAGE_NOT_EXACT")
    for group in manifest["groups"]:
        previous = same_event
        chain = group["receipt_chain_from_same_event"]
        require(bool(chain), "EMPTY_BASELINE_RECEIPT_CHAIN")
        for link in chain:
            require(link["field"] in ("signed_previous_biological_Root", "signed_previous_live_genomic_Root") and
                    bound_in(link["receipt"], [previous.get(link["field"], {})]), "OLD_RECEIPT_CHAIN_NOT_BOUND")
            previous = certified(link["receipt"])
        require(group["signed_receipt"] == chain[-1]["receipt"], "BASELINE_RECEIPT_NOT_CHAIN_ENDPOINT")
        sealed_binding = group["sealed_manifest"]
        require(bound_in(sealed_binding, [previous["sealed_new_current_reference_manifest"]]), "SEALED_MANIFEST_NOT_SIGNED")
        sealed = json.loads(read_bound(sealed_binding))
        for key in ("signed_owners", "signed_expressions"):
            require(bound_in(group[key], sealed["logical_refs"]), "RAW_PARTS_NOT_SEALED", artifact=key)
    return manifest, runpy.run_path(comparator_binding["path"])


def exact_coverage(raw_names, paid, summary):
    overlap = raw_names & paid
    require(overlap == EXPECTED_NAMES, "RAW_OWN_PAID_INTERSECTION_NOT_EXPECTED", actual=sorted(overlap))
    reported = summary.get("rechecked_paid_names")
    require(isinstance(reported, list) and set(reported) == overlap and len(reported) == 15,
            "SUMMARY_RECHECKED_SET_NOT_EXACT")
    return overlap


def binding(path, raw):
    return {"path": str(path), "sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)}


def audit(result, paid_path):
    manifest, tool = load_trust_chain()
    new_bindings = {}
    inputs = {}
    for name in ("owners.jsonl", "expressions.jsonl", "summary.json", "graph.jsonl"):
        path = result / ("ExecuteAudit." + name)
        inputs[name] = path.read_bytes()
        new_bindings[name] = binding(path, inputs[name])
    rows = tool["read_rows"](inputs["owners.jsonl"], result / "ExecuteAudit.owners.jsonl")
    new_dag = tool["DAG"].load(inputs["expressions.jsonl"], result / "ExecuteAudit.expressions.jsonl")
    by_name = defaultdict(list)
    for row in rows:
        by_name[row["name"]].append(row)
    paid_raw = paid_path.read_bytes()
    paid = set(paid_raw.decode().splitlines())
    summary = tool["decode_json"](inputs["summary.json"], result / "ExecuteAudit.summary.json")
    require(summary["raw"] == len(rows), "RAW_SLOT_COUNT")
    overlap = exact_coverage(set(by_name), paid, summary)
    graph_rows = tool["read_rows"](inputs["graph.jsonl"], result / "ExecuteAudit.graph.jsonl")
    graph = {row["name"]: row for row in graph_rows}
    require(len(graph) == len(graph_rows) == summary["visited_new_and_frontier"], "GRAPH_COUNT")
    comparisons = []
    for group in manifest["groups"]:
        old_rows = tool["read_rows"](read_bound(group["signed_owners"]), Path(group["signed_owners"]["path"]))
        old_dag = tool["DAG"].load(read_bound(group["signed_expressions"]), Path(group["signed_expressions"]["path"]))
        old_by_name = defaultdict(list)
        for row in old_rows:
            if row["name"] in group["exact_declarations"]:
                old_by_name[row["name"]].append(row)
        require(set(old_by_name) == set(group["exact_declarations"]), "EXACT_OLD_RAW_NAME_MISSING")
        for name in group["exact_declarations"]:
            node = graph.get(name)
            tool["verify_fresh_node"](node, name)
            checks = []
            for new_index, new in enumerate(by_name[name]):
                require(new["kind"] == "theorem" and new["name"] == name, "LAZY_KIND_NAME_CHANGED")
                for graph_key, owner_key in (("dependencies", "all_dependencies"),
                                             ("typeDependencies", "type_constants"), ("valueDependencies", "value_constants")):
                    require(set(node[graph_key]) == set(tool["metadata"](new)[owner_key]),
                            "FRESH_GRAPH_PARTS_MISMATCH", name=name, part=graph_key)
                require(node["kind"] == new["kind"] and not node["unsafe"] and not node["partial"], "FRESH_GRAPH_FLAGS")
                for old_index, old in enumerate(old_by_name[name]):
                    require(old["name"] == new["name"], "PRIVATE_OR_CONSTANT_NAME_REWRITTEN")
                    parts = tool["compare_owner"](new, new_dag, old, old_dag)
                    checks.append({"new_emission": new_index, "signed_emission": old_index,
                                   "new_module": new["module"], "new_canonical_module": new["canonical_module"],
                                   "signed_module": old["module"], "signed_canonical_module": old["canonical_module"],
                                   "parts": parts})
            comparisons.append({"name": name, "signed_receipt": group["signed_receipt"],
                                "sealed_manifest": group["sealed_manifest"], "signed_owners": group["signed_owners"],
                                "signed_expressions": group["signed_expressions"], "emissions": checks})
        del old_rows, old_dag, old_by_name
    require({row["name"] for row in comparisons} == overlap, "RECHECKED_NAME_SKIPPED")
    totals = {"expression_pairs": 0, "type_expression_pairs": 0, "value_expression_pairs": 0,
              "recursor_rhs_roots": 0, "alpha_bound_display_changes": 0, "emission_pairs": 0}
    for row in comparisons:
        for check in row["emissions"]:
            totals["emission_pairs"] += 1
            for key, part in check["parts"].items():
                parts = part if key == "recursor_rhs" else [part]
                if key == "recursor_rhs":
                    totals["recursor_rhs_roots"] += len(parts)
                for piece in parts:
                    totals["expression_pairs"] += piece["expression_pairs"]
                    totals["alpha_bound_display_changes"] += len(piece["alpha_bound_display_changes"])
                    if key == "type_root": totals["type_expression_pairs"] += piece["expression_pairs"]
                    if key == "value_root": totals["value_expression_pairs"] += piece["expression_pairs"]
    require(totals["alpha_bound_display_changes"] == 0, "EXACT_LAZY_EXPR_BOUND_NAMES_DIFFER")
    manifest_raw = MANIFEST.read_bytes()
    require(hashlib.sha256(manifest_raw).hexdigest() == MANIFEST_SHA, "MANIFEST_CHANGED_DURING_CHECK")
    return {"schema": "CPS1-native-registration-paid-lazy-lossless-comparison/v1", "verdict": "passed",
            "baseline_manifest": binding(MANIFEST, manifest_raw), "reused_signed_comparator": manifest["signed_reused_comparator"],
            "signed_current_parent_chain": [manifest["signed_parent_anchor"], *manifest["current_receipt_chain"]],
            "signed_prior_manifest": manifest["signed_prior_baseline_manifest"],
            "signed_same_event_receipt": manifest["signed_same_event_receipt"],
            "new_outputs": new_bindings, "paid_names": binding(paid_path, paid_raw),
            "raw_slots": len(rows), "expression_nodes": len(new_dag.rows),
            "exact_raw_own_paid_intersection": sorted(overlap), "exact_name_count": len(overlap),
            "complete_type_value_levels_kind_flags_metadata_recursor_rhs_identical": True,
            "fresh_graph_covered_all_rechecked_parts": True, "all_actual_raw_emissions_compared": True,
            "private_full_name_exact": True, "alpha_renaming_used": False,
            "storage_owner_and_DAG_ids_ignored_only": True, "old_raw_exports": 0, "math_compiles": 0,
            "raw_artifacts_copied": 0, "totals": totals, "comparisons": comparisons}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("result_dir", type=Path)
    parser.add_argument("--paid-names", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    try:
        result = audit(args.result_dir, args.paid_names)
    except Exception as exc:
        result = {"schema": "CPS1-native-registration-paid-lazy-lossless-comparison/v1",
                  "verdict": "failed", "error": str(exc)}
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2, sort_keys=True) + "\n")
    if result["verdict"] == "passed":
        print(json.dumps({"verdict": "passed", "exact_name_count": result["exact_name_count"],
                          "totals": result["totals"]}, ensure_ascii=False))
        return 0
    print(json.dumps(result, ensure_ascii=False), file=sys.stderr)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
