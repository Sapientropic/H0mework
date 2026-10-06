#!/usr/bin/env python3
"""Recompute frozen response evidence; report directories supply receipts, never code or inputs."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import importlib.util
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
from types import FunctionType

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
FREEZE = "b818e92fbdeca40d4a34c26e4bbf5ad90a0a4f80"
VERSION = "nominal-response-r0006"
SCHEMA = "nist-response-verification/v1"
PRIMARY = "response.json"
INDEPENDENT = "independent_response.json"


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def parse_criterion(text):
    begin, end = "<!-- FROZEN-RESPONSE-BEGIN -->", "<!-- FROZEN-RESPONSE-END -->"
    require(text.count(begin) == text.count(end) == 1, "nonunique_response_criterion")
    block = text.split(begin)[1].split(end)[0].strip()
    require(block.startswith("```json\n") and block.endswith("```"), "invalid_response_criterion")
    config = json.loads(block[7:-3])
    found = re.findall(r"η([AB])\s*=\s*([\d.]+)\s*±\s*([\d.]+)", text)
    require(len(found) == 2 and {row[0] for row in found} == {"A", "B"}, "ambiguous_efficiency_text")
    for side, center, width in found:
        row = config["channel"]["eta_" + side]
        require(F(center) == F(row["center"]) and F(width) == F(row["half_width"]) == F(3, 1000),
                "efficiency_unit_mismatch")
    require(config["criterion_version"] == VERSION, "criterion_revision_mismatch")
    require(config["source_mapping_identified"] is False and config["production_admitted"] is False,
            "response_cannot_admit_empirical_source")
    require(config["rounding"]["original_gate_tolerances_modified"] is False, "original_gate_tolerance_changed")
    return config


def scientific_inputs():
    for name in ("criterion.md", "sources.json"):
        relative = (HERE/name).relative_to(ROOT).as_posix()
        committed = subprocess.check_output(["git", "show", FREEZE+":"+relative], cwd=ROOT)
        require(committed == (HERE/name).read_bytes(), "unfrozen_source_packet:"+name)
    config = parse_criterion((HERE/"criterion.md").read_text())
    packet = json.loads((HERE/"sources.json").read_text())
    bindings = {}
    for row in packet["inputs"]:
        path = (ROOT/row["path"]).resolve()
        require(path.is_relative_to(ROOT), "source_path_outside_workspace")
        require(digest(path) == row["sha256"], "source_binding_mismatch:"+row["path"])
        bindings[row["path"]] = row["sha256"]
    for name in ("criterion.md", "sources.json"):
        bindings[(HERE/name).relative_to(ROOT).as_posix()] = digest(HERE/name)
    return config, bindings


def implementation(name):
    spec = importlib.util.spec_from_file_location("_verified_nist_"+name, HERE/(name+".py"))
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def rational_bounds(row, *, lower_only=False):
    lo = F(row["exact_lower"])
    hi = None if lower_only else F(row["exact_upper"])
    require(hi is None or lo <= hi, "reversed_reported_interval")
    return lo, hi


def contains(row, value, *, lower_only=False):
    require(isinstance(value, (float, int)) and not isinstance(value, bool) and math.isfinite(value),
            "nonfinite_matrix_readout")
    lo, hi = rational_bounds(row, lower_only=lower_only)
    exact = F(value)
    return lo <= exact and (hi is None or exact <= hi)


def same_structure(actual, expected):
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return actual.keys() == expected.keys() and all(same_structure(actual[k], v) for k, v in expected.items())
    if isinstance(expected, list):
        return len(actual) == len(expected) and all(same_structure(a, b) for a, b in zip(actual, expected))
    return actual == expected


def validate_certification(bindings):
    receipt = json.loads((HERE/"certification.json").read_text())
    require(receipt["schema"] == "nist-raw-m3-response-certification/v1" and receipt["status"] == "certified",
            "missing_lean_certification")
    freeze = receipt["criterion_freeze"]
    require(freeze["commit"] == FREEZE and freeze["sha256"] == digest(HERE/"criterion.md"),
            "lean_criterion_binding_mismatch")
    for row in (receipt["candidate"], receipt["direct_consumer"]):
        require(digest(ROOT/row["file"]) == row["sha256"], "lean_candidate_or_consumer_binding_mismatch")
    for path, expected in receipt["bindings"].items():
        require(digest(ROOT/path) == expected, "lean_source_binding_mismatch:"+path)
    verification = receipt["focused_verification"]
    require(verification["fresh_source_compilation"] is True and verification["trust_level"] == 0
            and verification["warning_as_error"] is True and len(verification["commands"]) == 4
            and all(row["exit_code"] == 0 for row in verification["commands"])
            and "RESPONSE_CERTIFIED" in verification["commands"][-1]["stdout"], "invalid_lean_compile_receipt")
    require(receipt["axioms"] == ["propext", "Classical.choice", "Quot.sound"], "unauthorized_lean_axioms")
    for name in ("Response.lean", "ResponseCertification.lean", "certification.json"):
        bindings[(HERE/name).relative_to(ROOT).as_posix()] = digest(HERE/name)
    return receipt


class FormalField:
    """Rational functions in the independent matrix producer's sparse polynomial ring."""
    polynomial = None

    def __init__(self, numerator=0, denominator=None):
        p = self.polynomial
        self.numerator = p.cast(numerator)
        self.denominator = p(1) if denominator is None else p.cast(denominator)
        require(bool(self.denominator.coefficients), "zero_symbolic_denominator")
        if not self.numerator.coefficients:
            self.denominator = p(1)
        elif set(self.denominator.coefficients) == {()}:
            self.numerator /= self.denominator.coefficients[()]
            self.denominator = p(1)

    @classmethod
    def variable(cls, name):
        return cls(cls.polynomial.variable(name))

    @classmethod
    def cast(cls, value):
        return value if isinstance(value, cls) else cls(value)

    def __add__(self, other):
        other = self.cast(other)
        if self.denominator.coefficients == other.denominator.coefficients:
            return self.__class__(self.numerator+other.numerator, self.denominator)
        return self.__class__(self.numerator*other.denominator+other.numerator*self.denominator,
                              self.denominator*other.denominator)

    __radd__ = __add__

    def __neg__(self):
        return self.__class__(-self.numerator, self.denominator)

    def __sub__(self, other):
        return self + -self.cast(other)

    def __rsub__(self, other):
        return self.cast(other) + -self

    def __mul__(self, other):
        other = self.cast(other)
        return self.__class__(self.numerator*other.numerator, self.denominator*other.denominator)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.cast(other)
        return self.__class__(self.numerator*other.denominator, self.denominator*other.numerator)

    def __rtruediv__(self, other):
        return self.cast(other)/self

    def __pow__(self, exponent):
        require(isinstance(exponent, int) and exponent >= 0, "unsupported_symbolic_power")
        value = self.__class__(1)
        for _ in range(exponent):
            value *= self
        return value


def symbolic_source_check(primary, independent, config):
    class Field(FormalField):
        polynomial = independent.Polynomial

    variable = Field.variable
    r, ma, mb, ax, bx = (variable(name) for name in ("r", "az", "bz", "ax", "bx"))
    parameters = {"r": r, "q": variable("q"), "eta_A": variable("ea"), "eta_B": variable("eb"),
                  "mA": ma, "mB": mb, "xi": ax*bx, "zeta": ma*mb,
                  **{name: name for name in ("a0", "a1", "b0", "b1")}}
    def symbolic_axes(name, pi, terms):
        return variable("s"+name), variable("c"+name)
    # Run the actual primary function bodies, replacing only the four sine/cosine readouts.
    globals_ = {**primary.__dict__, "sin_cos": symbolic_axes}
    raw = FunctionType(primary.source_ch.__code__, globals_)(parameters, config, None, None)
    grouped = FunctionType(primary.grouped_ch.__code__, globals_)(parameters, config, None, None)
    replacements = {"delta": (r*r-1)/(1+r*r), "chi": 2*r/(1+r*r),
                    "ba": Field(F(config["channel"]["background_A_per_trial"])),
                    "bb": Field(F(config["channel"]["background_B_per_trial"]))}
    generated = Field(0)
    polynomial = independent.generated_score()
    for monomial, coefficient in polynomial.coefficients.items():
        term = Field(coefficient)
        for name, exponent in monomial:
            term *= replacements.get(name, variable(name))**exponent
        generated += term
    require(not (raw-generated).numerator.coefficients, "primary_raw_source_differs_from_matrix_polynomial")
    require(not (grouped-generated).numerator.coefficients, "grouped_CH_not_source_identity")
    require(all(dict(m).get("ea", 0) <= 1 and dict(m).get("eb", 0) <= 1
                for m in polynomial.coefficients), "CH_not_bilinear_in_efficiencies")
    independent.score_factorization()
    return {"primary_raw_equals_independent_matrix_polynomial": True,
            "primary_grouped_equals_independent_matrix_polynomial": True,
            "source_CH_bilinear_in_efficiencies": True,
            "method": "exact sparse polynomial numerator identities; primary code executed with formal trigonometric axes",
            "nonzero_source_denominator": "1+r^2"}


def matrix_recompute(independent, cases, config, instrument):
    """Use the current runtime or the configured bundled runtime, without mixing Python ABIs."""
    try:
        import numpy
    except ImportError:
        override = os.environ.get("P23_RESPONSE_PYTHON")
        executable = Path(override) if override else Path.home()/".cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3"
        require(executable.is_file(), "matrix_runtime_unavailable")
        probe = subprocess.run([str(executable), "-c", "import numpy"], capture_output=True, text=True, timeout=15)
        require(probe.returncode == 0, "matrix_runtime_probe_failed")
        script = """import json,sys
sys.path.insert(0,sys.argv[1])
import independent_response as i
import numpy
d=json.load(sys.stdin)
centers=[i.center_controls(c,d['config'],d['instrument']) for c in d['cases']]
controls=i.matrix_controls(d['config'],d['instrument'])
print(json.dumps({'centers':centers,'controls':controls,'runtime':sys.executable,'numpy_version':numpy.__version__}))
"""
        run = subprocess.run([str(executable), "-c", script, str(HERE)],
                             input=json.dumps({"cases": cases, "config": config, "instrument": instrument}),
                             capture_output=True, text=True, timeout=30)
        require(run.returncode == 0, "fresh_matrix_recomputation_failed:"+run.stderr[-1000:])
        payload = json.loads(run.stdout)
        return payload["centers"], payload["controls"], {"fresh": True, "runtime": payload["runtime"],
                                                     "numpy_version": payload["numpy_version"], "bundled_subprocess": True}
    centers = [independent.center_controls(case, config, instrument) for case in cases]
    return centers, independent.matrix_controls(config, instrument), {"fresh": True, "runtime": sys.executable,
                      "numpy_version": numpy.__version__, "bundled_subprocess": False}


@lru_cache(maxsize=4)
def recompute(program_fingerprint):
    config, _ = scientific_inputs()
    primary, independent = implementation("response"), implementation("independent_response")
    require(primary.load_frozen() == independent.load_frozen() == config, "criterion_parser_disagreement")
    symbolic = symbolic_source_check(primary, independent, config)
    main = primary.compute()
    instrument, base = independent.read_inputs(config)
    pi = independent.Interval(*config["interval"]["pi"])
    cases = []
    for name, limits in config["cases"].items():
        case = independent.case_result(name, limits, base, config, pi)
        cases.append(case)
    centers, controls, matrix_runtime = matrix_recompute(independent, cases, config, instrument)
    for case, center in zip(cases, centers):
        case["center_controls"] = center
    return config, primary, independent, main, cases, controls, symbolic, instrument, matrix_runtime


def validate_tree(positive, config):
    addresses = [row["address"] for row in positive["leaves"]]
    require(len(addresses) == positive["leaf_count"] and 0 < len(addresses) <= config["interval"]["max_leaves"],
            "invalid_refinement_leaf_count")
    require(len(set(addresses)) == len(addresses) and all(set(a) <= {"0", "1"} for a in addresses),
            "invalid_refinement_address")
    require(max(map(len, addresses)) == positive["max_depth_used"] <= config["interval"]["max_depth"],
            "invalid_refinement_depth")
    leaves = set(addresses)
    prefixes = {a[:i] for a in addresses for i in range(len(a)+1)}
    def complete(node):
        if node in leaves:
            return not any(a != node and a.startswith(node) for a in addresses)
        return node+"0" in prefixes and node+"1" in prefixes and complete(node+"0") and complete(node+"1")
    require(complete(""), "refinement_does_not_cover_whole_domain")
    require(positive["split_order"] == config["interval"]["split_order"], "refinement_split_order_changed")


def validate_cases(primary, own, expected_main, expected_cases, config, independent, instrument):
    require(same_structure(primary, expected_main), "primary_recomputation_mismatch")
    require(same_structure(own["cases"], expected_cases), "independent_recomputation_mismatch")
    reports = []
    for main, case in zip(primary["cases"], own["cases"]):
        require(main["case"] == case["case"], "case_identity_mismatch")
        pbox = {key: rational_bounds(value) for key, value in main["box"].items()}
        ibox = {key.removesuffix("_deg"): rational_bounds(value) for key, value in case["continuous_domain"].items()}
        require(pbox == ibox, "continuous_domain_mismatch")
        positive = main["orientation_preserving_positive_branch"]
        validate_tree(positive, config)
        center = expected_cases[len(reports)]["center_controls"]
        prefactor = center["q"] * float(F(config["channel"]["eta_A"]["center"])) * float(F(config["channel"]["eta_B"]["center"]))
        sides = {}
        for side in ("alice", "bob"):
            physical = center["responses"][side]["physical"]
            normalized = physical/prefactor
            ratio = center["responses"][side]["required_xi_over_zeta"]
            for report in (main, case):
                response = report["responses"][side]
                require(contains(response["physical"], physical), "matrix_physical_center_outside_enclosure")
                require(contains(response["required_xi_over_zeta"], ratio), "matrix_ratio_center_outside_enclosure")
                lo, hi = rational_bounds(response["physical"])
                sign = "negative" if hi < 0 else "positive" if lo > 0 else None
                require(sign == response["sign"] and response["stationarity_excluded"] is (sign is not None),
                        "incorrect_reported_derivative_sign")
            require(contains(main["responses"][side]["normalized"], 2*normalized)
                    and contains(case["responses"][side]["normalized"], normalized), "normalized_response_unit_mismatch")
            require(main["responses"][side]["sign"] == case["responses"][side]["sign"], "physical_sign_disagreement")
            sides[side] = {"physical": main["responses"][side]["physical"],
                           "independent_physical": case["responses"][side]["physical"],
                           "sign": main["responses"][side]["sign"], "matrix_center": physical}
        for name, improvement in center["fixed_update_improvements"].items():
            require(contains(main["fixed_updates"][name]["improvement"], improvement, lower_only=True)
                    and contains(case["fixed_updates"][name]["improvement"], improvement), "matrix_update_outside_enclosure")
        require(contains(positive["CH"], center["CH"])
                and contains(case["orientation_preserving_positive_branch"]["CH"], center["CH"]),
                "matrix_CH_center_outside_enclosure")
        require(positive["restriction"] == case["orientation_preserving_positive_branch"]["restriction"] ==
                config["robust_positive_branch"]["restriction"], "conditional_orientation_scope_mismatch")
        require(case["orientation_preserving_positive_branch"]["claim_is_conditional"] is True,
                "conditional_CH_scope_missing")
        reports.append({"case": case["case"], "responses": sides,
                        "fixed_updates": {name: {"primary_lower": main["fixed_updates"][name]["improvement"]["exact_lower"],
                                                 "independent": row["improvement"]}
                                          for name, row in case["fixed_updates"].items()},
                        "conditional_CH": positive["CH"],
                        "independent_conditional_CH": case["orientation_preserving_positive_branch"]["CH"],
                        "refinement_leaves_verified": positive["leaf_count"]})
    return reports


def assess(report_dir=None, *, enabled=True):
    base = {"schema": SCHEMA, "criterion_version": VERSION, "source_mapping_identified": False,
            "production_admitted": False, "evidence_valid": False}
    if not enabled:
        return {**base, "status": "disabled_by_override"}
    directory = HERE if report_dir is None else Path(report_dir)
    try:
        config, sources = scientific_inputs()
        certification = validate_certification(sources)
        primary_bytes, independent_bytes = (directory/PRIMARY).read_bytes(), (directory/INDEPENDENT).read_bytes()
        primary_hash = hashlib.sha256(primary_bytes).hexdigest()
        independent_hash = hashlib.sha256(independent_bytes).hexdigest()
        primary, own = json.loads(primary_bytes), json.loads(independent_bytes)
        for report, schema in ((primary, "nist-response-primary/v1"), (own, "nist-response-independent/v1")):
            require(report["schema"] == schema and report["criterion_version"] == VERSION, "response_revision_mismatch")
            require(report["source_mapping_identified"] is False and report["production_admitted"] is False,
                    "research_receipt_cannot_admit_production")
        psource = {k: v for k, v in sources.items() if not k.endswith(("ResponseCertification.lean", "certification.json"))}
        psource[(HERE/"response.py").relative_to(ROOT).as_posix()] = digest(HERE/"response.py")
        require(primary["bindings"] == psource, "primary_source_binding_mismatch")
        isource = {k: v for k, v in psource.items() if not k.endswith(("response.py", "Response.lean"))}
        isource[(HERE/"independent_response.py").relative_to(ROOT).as_posix()] = digest(HERE/"independent_response.py")
        primary_path = (HERE/PRIMARY).relative_to(ROOT).as_posix()
        isource[primary_path] = primary_hash
        require(own["bindings"] == isource, "independent_source_binding_mismatch")
        fingerprint = tuple(sorted(sources.items())) + (("primary_program", digest(HERE/"response.py")),
            ("independent_program", digest(HERE/"independent_response.py")),
            ("matrix_python_override", os.environ.get("P23_RESPONSE_PYTHON", "")))
        config, p, i, expected_main, expected_cases, controls, symbolic, instrument, matrix_runtime = recompute(fingerprint)
        require(primary["criterion_freeze"] == p.criterion_freeze()
                and own["criterion_freeze"] == i.criterion_freeze(), "response_freeze_mismatch")
        require(own["scope"] == config["scope"], "independent_scope_mismatch")
        require(own["calculation_implementation"]["scientific_ast_sha256"] == i.computation_ast_digest()
                and own["calculation_implementation"]["primary_artifact_used_as_input"] is False,
                "independent_calculation_provenance_mismatch")
        require(same_structure(own["matrix_controls"], controls) and controls["passed"] is True, "matrix_control_recomputation_mismatch")
        require(own["symbolic_source_certificate"]["normalized_primed_derivatives"] ==
                {side: pol.json() for side, pol in zip(("alice", "bob"), i.generated_responses())},
                "symbolic_matrix_response_mismatch")
        require(own["symbolic_source_certificate"]["full_CH_bilinear_in_efficiencies"] is True
                and own["symbolic_source_certificate"]["full_CH_factorization_verified"] is True,
                "invalid_symbolic_matrix_certificate")
        cases = validate_cases(primary, own, expected_main, expected_cases, config, i, instrument)
        verdict = "CERTIFIED" if all(c["verdict"] == "CERTIFIED" and c["center_controls"]["inside_own_enclosures"]
                                     for c in expected_cases) and controls["passed"] else "NOT_CERTIFIED"
        require(own["verdict"] == verdict, "incorrect_independent_verdict")
        require(own["comparison"]["primary_artifact_sha256"] == primary_hash
                and own["comparison"]["primary_bindings"] == primary["bindings"], "comparison_binding_mismatch")
        require(own["comparison"]["normalization"] == {
            "independent": "dS/(q eta_A eta_B)", "primary": "2 dS/(q eta_A eta_B)",
            "primary_to_independent": "divide by 2", "derivative_angle_unit": "radian",
            "control_angle_unit": "degree"}, "comparison_unit_metadata_mismatch")
        require(own["comparison"]["source_bindings_agree"] is True and own["comparison"]["freeze_agrees"] is True
                and own["comparison"]["passed"] is True, "independent_comparison_failed")
        require([row["case"] for row in own["comparison"]["cases"]] == list(config["cases"])
                and all(row["passed"] is True for row in own["comparison"]["cases"]), "incomplete_independent_comparison")
        source_records = {**sources, (HERE/"response.py").relative_to(ROOT).as_posix(): digest(HERE/"response.py"),
                          (HERE/"independent_response.py").relative_to(ROOT).as_posix(): digest(HERE/"independent_response.py"),
                          (HERE/"verify.py").relative_to(ROOT).as_posix(): digest(HERE/"verify.py"),
                          "response.json": primary_hash, "independent_response.json": independent_hash}
        require(digest(directory/PRIMARY) == primary_hash and digest(directory/INDEPENDENT) == independent_hash,
                "response_artifact_changed_during_verification")
        return {**base, "status": "verified", "evidence_valid": True,
                "criterion_freeze": p.criterion_freeze(), "bindings": source_records,
                "lean_candidate_certified": certification["status"] == "certified",
                "symbolic_source_identity": symbolic, "continuous_cases": cases,
                "matrix_controls_recomputed": True,
                "matrix_runtime": matrix_runtime,
                "maximum_preparation_calibration_same": controls["maximum_preparation_full_matrix_agreement_error"] <=
                    float(F(config["matrix_controls"]["probability_tolerance"])),
                "nonmaximum_margins_differ": controls["nonmaximum_preparation_margin_difference"] >
                    float(F(config["matrix_controls"]["probability_tolerance"])),
                "normalized_convention": "primary normalized = 2 * independent normalized; physical derivative is per radian",
                "scope": config["scope"], "verification_role": "exact-rational program verification linked to separately certified symbolic Lean response; not a Lean proof of numeric signs"}
    except FileNotFoundError as error:
        return {**base, "status": "missing_response_evidence", "reason": str(error)}
    except (ValueError, KeyError, TypeError, IndexError, AttributeError, ArithmeticError, ImportError, OSError, subprocess.SubprocessError) as error:
        return {**base, "status": "invalid_response_evidence", "reason": str(error)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only", action="store_true", help="read and recompute without writing receipts")
    parser.add_argument("--directory", type=Path, help="explicit receipt directory override; inputs and code stay fixed")
    parser.add_argument("--disabled", action="store_true")
    args = parser.parse_args()
    result = assess(args.directory, enabled=not args.disabled)
    print(json.dumps(result, indent=2))
    return 0 if result["status"] == "verified" else 1


if __name__ == "__main__":
    raise SystemExit(main())
