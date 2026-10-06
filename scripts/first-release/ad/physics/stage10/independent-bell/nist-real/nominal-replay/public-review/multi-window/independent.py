#!/usr/bin/env python3
"""Independent rational multi-window count, confidence, and necessary-pulse readout."""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import json
import math
from pathlib import Path, PurePosixPath
import posixpath
import re
import subprocess
import time
import xml.etree.ElementTree as ET
import zipfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[7]
PUBLIC = HERE.parent / "public-summaries"
VERSION = "p23-public-multi-window-mw0001"
SCHEMA = "p23-public-multi-window-independent/v1"
SOURCE_FREEZE = "89cd2e5039"
CONTRACT_FREEZE = "dcd53e8384"
SCALE = 10 ** 60
LABELS = {"5": [6], "456": [5, 6, 7], "34567": [4, 5, 6, 7, 8],
          "2345678": [3, 4, 5, 6, 7, 8, 9], "123456789": list(range(2, 11))}
FILES = {"diag-02-54.xlsx", "diag-03-43.xlsx", "diag-19-45.xlsx", "diag-xor1.xlsx", "diag-xor2.xlsx", "diag-xor3.xlsx"}
NS = {"s": "http://schemas.openxmlformats.org/spreadsheetml/2006/main",
      "r": "http://schemas.openxmlformats.org/officeDocument/2006/relationships",
      "p": "http://schemas.openxmlformats.org/package/2006/relationships"}


def require(value, reason):
    if not value:
        raise ValueError(reason)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def ceiling(n, d):
    return -((-n) // d)


@dataclass(frozen=True)
class I:
    lo: F
    hi: F

    def __init__(self, lo=0, hi=None):
        lo, hi = F(lo), F(lo if hi is None else hi)
        require(lo <= hi, "reversed_rational_interval")
        object.__setattr__(self, "lo", F(lo.numerator * SCALE // lo.denominator, SCALE))
        object.__setattr__(self, "hi", F(ceiling(hi.numerator * SCALE, hi.denominator), SCALE))

    def __add__(self, other):
        other = other if isinstance(other, I) else I(other)
        return I(self.lo + other.lo, self.hi + other.hi)

    __radd__ = __add__

    def __neg__(self):
        return I(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + -(other if isinstance(other, I) else I(other))

    def __rsub__(self, other):
        return I(other) + -self

    def __mul__(self, other):
        other = other if isinstance(other, I) else I(other)
        vals = [a * b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return I(min(vals), max(vals))

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = other if isinstance(other, I) else I(other)
        require(not other.lo <= 0 <= other.hi, "rational_division_through_zero")
        return self * I(1 / other.hi, 1 / other.lo)

    def power(self, n):
        require(type(n) is int and n >= 0 and self.lo >= 0, "invalid_positive_power")
        if n == 0:
            return I(1)
        if n % 2:
            return self * self.power(n - 1)
        half = self.power(n // 2)
        return half * half

    def intersect(self, other):
        lo, hi = max(self.lo, other.lo), min(self.hi, other.hi)
        return None if lo > hi else I(lo, hi)


def packet(value):
    if isinstance(value, I):
        return {"exact_lower": str(value.lo), "exact_upper": str(value.hi),
                "lower": float(value.lo), "upper": float(value.hi)}
    if isinstance(value, F):
        return str(value)
    if isinstance(value, dict):
        return {k: packet(v) for k, v in value.items()}
    if isinstance(value, (tuple, list)):
        return [packet(v) for v in value]
    return value


def frozen(path, commit=None):
    path = Path(path).resolve()
    require(path.is_relative_to(ROOT), "foreign_scientific_source")
    rel = path.relative_to(ROOT).as_posix()
    if commit is None:
        commit = subprocess.check_output(["git", "log", "-1", "--format=%H", "--", rel], cwd=ROOT, text=True).strip()
    require(commit and subprocess.check_output(["git", "show", commit + ":" + rel], cwd=ROOT) == path.read_bytes(),
            "unfrozen_multi_window_source:" + rel)
    subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
    return {"path": rel, "commit": commit, "sha256": sha(path.read_bytes())}


def configuration(inputs_path=None):
    contract = frozen(HERE / "criterion.md", CONTRACT_FREEZE)
    source = frozen(HERE / "sources.json", CONTRACT_FREEZE)
    text = (HERE / "criterion.md").read_text()
    matches = re.findall(r"<!-- MW-FROZEN-BEGIN -->\s*```json\s*(.*?)\s*```\s*<!-- MW-FROZEN-END -->", text, re.S)
    require(len(matches) == 1, "nonunique_multi_window_contract")
    spec = json.loads(matches[0])
    require(spec["version"] == VERSION and spec["alpha"] == "1/20" and spec["features"] == 16 and
            spec["runs_covered"] == 6 and spec["pulse_subsets_covered"] == 32767 and
            spec["lambda_grid"] == {"powers_of_two": [1, 20], "positive_and_negative": True} and
            spec["settings_predictability"] == "3/1000" and spec["rational_exp_terms"] == 48 and
            spec["rational_log_terms"] == 128 and spec["root_precision_digits"] == 50 and
            spec["pulse_counts"] == [1, 3, 5, 7, 9] and spec["spacelike_review_pulse_counts"] == [1, 3, 5, 7] and
            spec["local_bet_grid_powers"] == [1, 20] and spec["source_epoch_policy"] == "distinct_run_sources_shared_within_each_run" and
            spec["complete_counts_required"] is True and spec["retrospective"] is True and spec["bell_event_files_read"] == 0,
            "multi_window_contract_changed")
    manifest = json.loads((HERE / "sources.json").read_text())
    require(manifest["version"] == VERSION and manifest["source_freeze"] == SOURCE_FREEZE, "wrong_multi_window_source_manifest")
    for row in manifest["inputs"]:
        p = (ROOT / row["path"]).resolve()
        require(p.is_relative_to(ROOT) and sha(p.read_bytes()) == row["sha256"], "multi_window_source_changed:" + row["path"])
    canonical_inputs = (HERE / spec["inputs"]).resolve()
    require(canonical_inputs == PUBLIC / "inputs.json", "foreign_workbook_input_location")
    frozen(canonical_inputs, SOURCE_FREEZE)
    selected = canonical_inputs if inputs_path is None else Path(inputs_path)
    require(selected.read_bytes() == canonical_inputs.read_bytes(), "lookalike_or_changed_input_override")
    return spec, json.loads(selected.read_text()), {"criterion": contract, "sources": source,
        "inputs": frozen(canonical_inputs, SOURCE_FREEZE), "input_override_is_same_bytes": inputs_path is not None,
        "manifest": manifest, "program": frozen(__file__)}


def workbook_parts(path):
    with zipfile.ZipFile(path) as archive:
        names = archive.namelist()
        require(len(names) == len(set(names)) and all(not PurePosixPath(n).is_absolute() and ".." not in PurePosixPath(n).parts for n in names),
                "unsafe_or_duplicate_workbook_part")
        require(all(info.file_size < 10_000_000 for info in archive.infolist()), "oversized_workbook_XML")
        relroot = ET.fromstring(archive.read("xl/_rels/workbook.xml.rels"))
        rels = {}
        for rel in relroot:
            rid = rel.attrib["Id"]
            require(rid not in rels, "duplicate_workbook_relationship")
            rels[rid] = rel.attrib
        root = ET.fromstring(archive.read("xl/workbook.xml"))
        result = {}
        for sheet in root.findall("s:sheets/s:sheet", NS):
            name = sheet.attrib["name"]
            rid = sheet.attrib["{" + NS["r"] + "}id"]
            require(name not in result and rid in rels, "missing_or_duplicate_sheet_binding")
            rel = rels[rid]
            require(rel.get("TargetMode") != "External" and rel["Type"].endswith("/worksheet"), "external_or_wrong_sheet_relationship")
            target = rel["Target"]
            part = posixpath.normpath(target.lstrip("/") if target.startswith("/") else "xl/" + target)
            require(part.startswith("xl/worksheets/") and ".." not in PurePosixPath(part).parts and part in names, "invalid_sheet_XML_target")
            xml = archive.read(part)
            result[name] = {"relationship_id": rid, "xml_part": part, "XML": xml,
                            "xml_sha256": sha(xml), "formula_count": len(ET.fromstring(xml).findall(".//s:f", NS))}
        return result


def literal_counts(xml):
    root = ET.fromstring(xml)
    by_ref = {}
    for cell in root.findall(".//s:sheetData/s:row/s:c", NS):
        ref = cell.attrib["r"]
        require(ref not in by_ref, "duplicate_sheet_cell")
        by_ref[ref] = cell
    counts = []
    for col in "ABCDEFGHIJKLMNOP":
        ref = col + "1"
        require(ref in by_ref, "missing_count_cell:" + ref)
        cell = by_ref[ref]
        require(cell.find("s:f", NS) is None and cell.attrib.get("t", "n") == "n", "nonliteral_or_formula_count:" + ref)
        value = cell.find("s:v", NS)
        require(value is not None and value.text is not None and re.fullmatch(r"0|[1-9][0-9]*", value.text) is not None,
                "invalid_integer_count:" + ref)
        counts.append(int(value.text))
    require(sum(counts) > 0, "empty_count_exposure")
    rows = [counts[j:j + 4] for j in range(0, 16, 4)]
    require(all(sum(row) > 0 for row in rows), "missing_setting_exposure")
    return rows


def read_workbooks(inputs):
    require(inputs["schema"] == "p23-public-small-workbook-inputs/v1" and
            inputs["settings_order"] == ["ab", "ab_prime", "a_prime_b", "a_prime_b_prime"] and
            inputs["outcomes_order"] == ["++", "+0", "0+", "00"], "changed_count_semantics")
    books = inputs["diagnostic_workbooks"]
    require(len(books) == 6 and {book["file"] for book in books} == FILES, "missing_or_lookalike_diagnostic_run")
    outputs = []
    for book in books:
        path = PUBLIC / book["file"]
        require(path.stat().st_size == book["bytes"] and sha(path.read_bytes()) == book["sha256"], "changed_workbook_bytes")
        parts = workbook_parts(path)
        require(set(parts) == set(LABELS), "missing_or_wrong_pulse_sheet")
        metadata = {group["sheet"]: group for group in book["groups"]}
        require(len(metadata) == len(book["groups"]) == 5 and set(metadata) == set(LABELS), "duplicate_or_missing_group")
        groups, exposures = [], []
        for label, pulses in LABELS.items():
            part, expected = parts[label], metadata[label]
            counts = literal_counts(part["XML"])
            N = sum(map(sum, counts))
            require(part["relationship_id"] == expected["relationship_id"] and part["xml_part"] == expected["xml_part"] and
                    counts == expected["counts"] and N == expected["complete_trials_literal_count_sum"] and
                    expected["paper_pulse_numbers"] == pulses and expected["pulse_count"] == len(pulses) and
                    expected["cell_range"] == "A1:P1", "independent_XML_extraction_disagrees_with_frozen_inputs")
            exposures.append(N)
            groups.append({"sheet": label, "paper_pulse_numbers": pulses, "pulse_count": len(pulses), "counts": counts,
                           "complete_trials": N, "relationship_id": part["relationship_id"], "xml_part": part["xml_part"],
                           "xml_sha256": part["xml_sha256"], "count_formulas_executed": 0,
                           "cached_diagnostic_formulas_not_used": part["formula_count"],
                           "spacelike_review_scope": len(pulses) in (1, 3, 5, 7)})
        require(len(set(exposures)) == 1, "mismatched_same_run_exposure")
        outputs.append({"run": book["file"][5:-5], "workbook": book["file"], "url": book["url"],
                        "sha256": book["sha256"], "complete_trials": exposures[0], "groups": groups})
    rate = inputs["rate_estimates"]
    rate_path = PUBLIC / rate["file"]
    require(rate["file"] == "rate-estimates.xlsx" and sha(rate_path.read_bytes()) == rate["sha256"], "changed_rate_workbook")
    inventory = workbook_parts(rate_path)
    return outputs, {"file": rate["file"], "sha256": rate["sha256"], "sheets": {
        name: {k: row[k] for k in ("relationship_id", "xml_part", "xml_sha256", "formula_count")} for name, row in inventory.items()},
        "formula_execution_count": 0, "values_used_for_CI_or_source": False}


@lru_cache(maxsize=128)
def exp_small(x, terms=48):
    x = F(x)
    require(abs(x) <= F(1, 2) and terms == 48, "exp_outside_frozen_Taylor_domain")
    polynomial, term = F(1), F(1)
    for n in range(1, terms + 1):
        term *= x / n
        polynomial += term
    radius = abs(x)
    remainder = radius ** (terms + 1) / math.factorial(terms + 1) / (1 - radius / (terms + 2))
    return I(polynomial - remainder, polynomial + remainder)


def log_unit(x, terms=128):
    x = F(x)
    require(1 <= x <= 2 and terms == 128, "log_outside_reduced_atanh_domain")
    t = (x - 1) / (x + 1)
    partial, power = F(0), t
    for j in range(terms):
        partial += 2 * power / (2 * j + 1)
        power *= t * t
    tail = 2 * power / (2 * terms + 1) / (1 - t * t)
    return I(partial, partial + tail)


@lru_cache(maxsize=256)
def logarithm(x):
    x = F(x)
    require(x > 0, "nonpositive_logarithm")
    exponent = x.numerator.bit_length() - x.denominator.bit_length()
    reduced = x / F(2) ** exponent
    while reduced < 1:
        exponent -= 1; reduced *= 2
    while reduced > 2:
        exponent += 1; reduced /= 2
    return log_unit(reduced) + exponent * log_unit(F(2))


def exp_interval(value):
    radius, steps = max(abs(value.lo), abs(value.hi)), 0
    while radius > F(1, 2):
        radius /= 2; steps += 1
    low = exp_small(value.lo / 2 ** steps).lo
    high = exp_small(value.hi / 2 ** steps).hi
    result = I(max(0, low), high)
    for _ in range(steps):
        result = result * result
    return result


def integer_root(value, n):
    require(value >= 0 and type(n) is int and n > 0, "invalid_integer_root")
    if value == 0:
        return 0
    lo, hi = 0, 1 << ((value.bit_length() + n - 1) // n)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid ** n <= value:
            lo = mid
        else:
            hi = mid
    return hi if hi ** n <= value else lo


def nth_root(value, n, digits=50):
    require(type(n) is int and n in (1, 3, 5, 7, 9) and digits == 50 and 0 <= value.lo <= value.hi <= 1,
            "invalid_probability_root")
    scale = 10 ** digits
    low_num = value.lo.numerator * scale ** n
    high_num = value.hi.numerator * scale ** n
    low = integer_root(low_num // value.lo.denominator, n)
    high = integer_root(high_num // value.hi.denominator, n)
    high += high ** n * value.hi.denominator < high_num
    return I(F(low, scale), F(high, scale))


def statistics(spec):
    epsilon = F(spec["settings_predictability"])
    pi_lo, pi_hi = (1 - epsilon) ** 2 / 4, (1 + epsilon) ** 2 / 4
    delta = F(spec["alpha"]) / (spec["features"] * 40 * spec["runs_covered"] * spec["pulse_subsets_covered"])
    threshold = logarithm(1 / delta)
    bets = [(F(sign, 2 ** power), exp_small(F(sign, 2 ** power))) for power in range(1, 21) for sign in (-1, 1)]
    return {"alpha": spec["alpha"], "delta": delta, "log_one_over_delta": threshold, "pi": [pi_lo, pi_hi], "bets": bets,
            "feature_global_allocation": [16, 40, 6, 32767], "Taylor_degree": 48, "atanh_terms": 128}


def confidence(count, N, stat):
    require(type(count) is int and type(N) is int and N > 0 and 0 <= count <= N, "invalid_count_or_exposure")
    lower, upper, grid = F(0), F(N), []
    for lam, exponential in stat["bets"]:
        bound = (I(lam * count) - stat["log_one_over_delta"]) / (exponential - 1)
        if lam > 0:
            lower = max(lower, bound.lo)
        else:
            upper = min(upper, bound.hi)
        grid.append({"lambda": lam, "exp_lambda": exponential, "predictable_mean_bound": bound})
    require(lower <= upper, "feature_mean_CI_empty")
    mean = I(lower, upper)
    probability = (mean / (N * I(stat["pi"][0], stat["pi"][1]))).intersect(I(0, 1))
    return {"count": count, "complete_trials": N, "predictable_count_CI": mean,
            "common_Born_CI": probability, "common_Born_compatible": probability is not None, "all_40_bets": grid}


def local_e_bets(counts, spec):
    wins, losses = counts[0][0], counts[1][1] + counts[2][2] + counts[3][0]
    epsilon = F(spec["settings_predictability"])
    ratio = ((1 + epsilon) / (1 - epsilon)) ** 2
    q0 = ratio / (1 + ratio)
    grid, total = [], I(0)
    for k in range(1, 21):
        fraction = F(1, 2 ** k)
        p = q0 + (1 - q0) * fraction
        win_multiplier, loss_multiplier = p / q0, (1 - p) / (1 - q0)
        logE = wins * logarithm(win_multiplier) + losses * logarithm(loss_multiplier)
        evalue = exp_interval(logE)
        total += evalue / 20
        grid.append({"power": k, "p": p, "win_multiplier": win_multiplier, "loss_multiplier": loss_multiplier,
                     "log_evalue": logE, "evalue": evalue})
    def pvalue(family):
        return I(0 if total.hi <= 0 else min(F(1), F(family) / total.hi),
                 1 if total.lo <= 0 else min(F(1), F(family) / total.lo))
    return {"wins": wins, "losses": losses, "setting_ratio": ratio, "q0": q0, "all_20_fixed_bets": grid,
            "e_mixture": total, "individual_anytime_p_upper": pvalue(1),
            "all_six_runs_and_masks_p_upper": pvalue(6 * 32767), "XOR3_four_named_windows_p_upper": pvalue(4),
            "original_paper_pvalue_recertified": False, "blind_selection_claimed": False}


def features(group, stat, spec):
    rows, N = group["counts"], group["complete_trials"]
    result = {"j": [], "sA_cell": [], "sB_cell": []}
    receipts = []
    for field, column_indices in (("j", (0,)), ("sA_cell", (0, 1)), ("sB_cell", (0, 2))):
        for row, counts in enumerate(rows):
            cert = confidence(sum(counts[i] for i in column_indices), N, stat)
            result[field].append(cert["common_Born_CI"])
            receipts.append({"field": field, "row": row, **cert})
    return {**group, "common_Born_CI": result, "all_feature_receipts": receipts,
            "local_fixed_bet_review": local_e_bets(rows, spec)}


def local_intersections(window):
    ci = window["common_Born_CI"]
    if any(value is None for field in ci.values() for value in field):
        return {name: None for name in ("QA0", "QA1", "QB0", "QB1")}
    intersections = {"QA0": ci["sA_cell"][0].intersect(ci["sA_cell"][1]),
                     "QA1": ci["sA_cell"][2].intersect(ci["sA_cell"][3]),
                     "QB0": ci["sB_cell"][0].intersect(ci["sB_cell"][2]),
                     "QB1": ci["sB_cell"][1].intersect(ci["sB_cell"][3])}
    return intersections


def pulse_intervals(window, spec):
    local = local_intersections(window)
    if any(v is None for v in local.values()):
        return {"status": "REJECTED_SAME_LOCAL_SETTING_INTERSECTION", "local_single_CI": local,
                "original_common_Born_CI": window["common_Born_CI"]}
    ba, bb = map(F, spec["background_per_pulse"])
    roots = {}
    for name, value in local.items():
        background = ba if name.startswith("QA") else bb
        roots[name] = (nth_root(1 - value, window["pulse_count"]) / (1 - background)).intersect(I(0, 1))
    joint_provenance = []
    for row, joint in enumerate(window["common_Born_CI"]["j"]):
        ai, bi = divmod(row, 2)
        noclick = (1 - local["QA" + str(ai)] - local["QB" + str(bi)] + joint).intersect(I(0, 1))
        value = None if noclick is None else (nth_root(noclick, window["pulse_count"]) / ((1 - ba) * (1 - bb))).intersect(I(0, 1))
        roots["QAB" + str(ai) + str(bi)] = value
        joint_provenance.append({"row": row, "joint_no_click_window": noclick, "joint_CI": joint})
    return {"status": "ROOT_NECESSARY_INTERVALS_GENERATED", "pulse_count": window["pulse_count"],
            "local_single_CI": local, "bare_single_pulse_no_click": roots, "joint_no_click_sources": joint_provenance,
            "background_removed_after_Nth_root": True}


def necessary_intersection(windows, spec, include_nine):
    selected = [w for w in windows if include_nine or w["pulse_count"] in (1, 3, 5, 7)]
    packets = [{"N": w["pulse_count"], "sheet": w["sheet"], "necessary": pulse_intervals(w, spec)} for w in selected]
    names = ["QA0", "QA1", "QB0", "QB1", "QAB00", "QAB01", "QAB10", "QAB11"]
    result, witnesses = {}, []
    for name in names:
        rows = []
        for view in packets:
            pulse = view["necessary"]
            value = pulse.get("bare_single_pulse_no_click", {}).get(name)
            rows.append({"N": view["N"], "sheet": view["sheet"], "interval": value})
        if any(row["interval"] is None for row in rows):
            result[name] = None
            witnesses.append({"coordinate": name, "reason": "window_local_or_physical_no_click_necessary_interval_empty", "windows": rows})
            continue
        lower = max(rows, key=lambda row: row["interval"].lo)
        upper = min(rows, key=lambda row: row["interval"].hi)
        lo, hi = lower["interval"].lo, upper["interval"].hi
        result[name] = None if lo > hi else I(lo, hi)
        if lo > hi:
            witnesses.append({"coordinate": name, "reason": "strict_Nth_root_intersection_empty", "lower_witness": lower,
                              "upper_witness": upper, "strict_lower": lo, "strict_upper": hi})
    return {"pulse_counts": [w["pulse_count"] for w in selected], "window_views": packets,
            "common_bare_single_pulse_no_click": result, "strict_empty_intersection_witnesses": witnesses,
            "identical_fresh_pulse_necessary_relations_compatible": not witnesses,
            "verdict": "NECESSARY_RELATIONS_NONEMPTY" if not witnesses else "IDENTICAL_PULSE_NECESSARY_RELATION_REJECTED",
            "Gaussian_source_existence_certified": False, "spacelike_qualification_extended_to_nine": False}


def science(inputs_path=None):
    start = time.monotonic()
    spec, inputs, bindings = configuration(inputs_path)
    parsed, rate_inventory = read_workbooks(inputs)
    stat = statistics(spec)
    runs = []
    for run in parsed:
        groups = [features(group, stat, spec) for group in run["groups"]]
        all_four = necessary_intersection(groups, spec, False)
        all_five = necessary_intersection(groups, spec, True)
        runs.append({**run, "groups": groups, "necessary_N1_N3_N5_N7": all_four, "necessary_including_N9": all_five,
                     "source_shared_within_run_only": True, "different_run_source_identified_as_same": False})
        print(json.dumps({"independent_run_complete": run["run"], "four_window_necessary": all_four["verdict"],
                          "including_nine_necessary": all_five["verdict"]}), flush=True)
    payload = packet({"schema": SCHEMA, "version": VERSION, "statistical_role": "retrospective_full_run_multi_window_review",
        "bindings": bindings, "statistics": stat, "runs": runs, "rate_workbook_inventory": rate_inventory,
        "all_360_feature_CI_and_14400_fixed_bets_retained": True,
        "all_six_runs_and_thirty_windows_retained": True, "XOR3_complete_trials": next(r["complete_trials"] for r in runs if r["run"] == "xor3"),
        "old_XOR3_stop_trials": 177358351, "overlapping_windows_multiplied_as_independent_likelihoods": False,
        "primary_new_program_or_outputs_read_before_first": False, "Gaussian_source_existence_certified": False,
        "source_stationarity_certified_by_counts": False, "settings_predictability_certified_by_counts": False,
        "retrospective": True, "bell_event_files_read": 0, "publication_configuration_identified": False,
        "actual_epoch_identified": False, "nominal_optimum_contract_replaced": False, "controller_advance": False})
    payload["source_stage_sha256"] = sha(json.dumps(payload, sort_keys=True, separators=(",", ":"), allow_nan=False).encode())
    payload["runtime_seconds"] = time.monotonic() - start
    return payload


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--inputs", type=Path)
    args = parser.parse_args()
    require(not args.output.exists(), "protected_existing_independent_multi_window_first")
    result = science(args.inputs)
    raw = (json.dumps(result, sort_keys=True, indent=2, allow_nan=False) + "\n").encode()
    args.output.write_bytes(raw)
    meta = {"schema": "p23-independent-multi-window-first-storage/v1", "version": VERSION, "logical_sha256": sha(raw),
            "logical_bytes": len(raw), "source_stage_sha256": result["source_stage_sha256"], "program": frozen(__file__)}
    args.output.with_name(args.output.stem + "-storage.json").write_text(json.dumps(meta, sort_keys=True, indent=2) + "\n")
    print(json.dumps(meta, sort_keys=True), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
