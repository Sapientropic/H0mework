#!/usr/bin/env python3
"""Recompute frozen collected-source responses; directories supply evidence, never code."""
from __future__ import annotations

import argparse
from fractions import Fraction as F
from functools import lru_cache
import hashlib
import importlib.util
import itertools
import json
import math
from pathlib import Path
import re
import subprocess
import sys
from types import FunctionType, MethodType, SimpleNamespace

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[6]
FREEZE = "4a8e1753f4e19669e11b39ac2c8987dc890f8f6f"
SOURCE_FREEZE = "a26869a1f3e5ec4dbe94230623235a6fe4411e53"
VERSION = "p23-collected-response-cr0001.1"
SCHEMA = "p23-collected-response-verification/v1"
CRITERION = "criterion-r0001.1.md"
PRIMARY = "response.json"
INDEPENDENT = "independent_response.json"
CASES = ("single_pair_lambda0", "M3_lambda1_calibration_envelope")
IDENTITY_KEYS = ("source_mapping_identified", "publication_configuration_identified", "production_admitted")
NORMALIZATION = "dCH/(Q*uA*uB*trace(OmegaAB)); derivative per radian"


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def relative(path):
    return Path(path).relative_to(ROOT).as_posix()


def same_structure(actual, expected):
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return actual.keys() == expected.keys() and all(same_structure(actual[k], v) for k, v in expected.items())
    if isinstance(expected, list):
        return len(actual) == len(expected) and all(same_structure(a, b) for a, b in zip(actual, expected))
    return actual == expected


def parse_criterion(text):
    begin, end = "<!-- CR-FROZEN-BEGIN -->", "<!-- CR-FROZEN-END -->"
    require(text.count(begin) == text.count(end) == 1, "nonunique_collected_response_criterion")
    blocks = re.findall(r"```json\s*(.*?)\s*```", text, re.S)
    require(len(blocks) == 1, "nonunique_collected_response_criterion")
    config = json.loads(blocks[0])
    require(config["version"] == VERSION, "criterion_revision_mismatch")
    require(all(config[k] is False for k in IDENTITY_KEYS), "conditional_criterion_cannot_admit_source")
    require(list(map(F, config["r_col"])) == [F("551/1923"), F("553/1921")], "printed_amplitude_rounding_mismatch")
    require(list(map(F, config["gamma"])) == [F("199/200"), F(1)], "conditional_coherence_domain_mismatch")
    require(F(config["q_max"]) == F("3/5000") and
            F(config["klyshko_min"]["A"]) == F("93/125") and
            F(config["klyshko_min"]["B"]) == F("753/1000"), "calibration_unit_mismatch")
    bound = F(config["q_max"])/(F(config["klyshko_min"]["A"])*F(config["klyshko_min"]["B"]))
    require(list(map(F, config["relative_M3_Z_correction"])) == [-bound, bound] == [-F("25/23343"), F("25/23343")],
            "calibration_budget_mismatch")
    require(config["q_identities"] == ["effective_pair", "collected_pair", "emitted_one_pair"], "q_identities_mismatch")
    require(list(map(F, config["paired_update_deg"])) == [F(0), -F(1, 20), F(0), F(1, 20)], "fixed_update_mismatch")
    require(config["controls"]["coordinate_regression"]["require_source_effect_common_permutation"] is True and
            config["controls"]["coordinate_regression"]["single_effect_swap_lookalike_must_fail"] is True,
            "coordinate_contract_mismatch")
    require(config["bell_event_files_read"] == 0, "unexpected_event_input")
    return config


def scientific_inputs():
    for name, commit in ((CRITERION, FREEZE), ("sources.json", SOURCE_FREEZE)):
        subprocess.run(["git", "merge-base", "--is-ancestor", commit, "HEAD"], cwd=ROOT, check=True)
        require(subprocess.check_output(["git", "show", commit+":"+relative(HERE/name)], cwd=ROOT) ==
                (HERE/name).read_bytes(), "unfrozen_source_packet:"+name)
    config = parse_criterion((HERE/CRITERION).read_text())
    packet = json.loads((HERE/"sources.json").read_text())
    require(packet["schema"] == "p23-collected-response-sources/v1" and
            all(packet[k] is False for k in IDENTITY_KEYS), "invalid_source_packet")
    require(packet["source_commits"] == ["40a278fec15e667ad393caa60527e55bc1247ab8",
                                         "67b5fa45a6223f191889eb34d74d05806d2a3351"], "original_source_history_mismatch")
    for commit in packet["source_commits"]:
        subprocess.run(["git", "merge-base", "--is-ancestor", commit, FREEZE], cwd=ROOT, check=True)
    bindings = {}
    for row in packet["inputs"]:
        path = (ROOT/row["path"]).resolve()
        require(path.is_relative_to(ROOT) and row["path"] not in bindings, "invalid_source_path")
        require(digest(path) == row["sha256"], "source_binding_mismatch:"+row["path"])
        bindings[row["path"]] = row["sha256"]
    old = HERE.parent/"investigation/collected-source/criterion.md"
    require(subprocess.check_output(["git", "show", packet["source_commits"][0]+":"+relative(old)], cwd=ROOT) ==
            old.read_bytes(), "original_collection_criterion_changed")
    for name in (CRITERION, "sources.json"):
        bindings[relative(HERE/name)] = digest(HERE/name)
    return config, bindings


def implementation(name):
    path = HERE/(name+".py")
    specification = importlib.util.spec_from_file_location("_cr_verified_"+name+digest(path)[:12], path)
    result = importlib.util.module_from_spec(specification)
    sys.modules[specification.name] = result
    specification.loader.exec_module(result)
    return result


def certification(bindings):
    receipt = json.loads((HERE/"certification.json").read_text())
    require(receipt["schema"] == "p23-collected-response-lean-certification/v1" and
            receipt["status"] == "certified", "missing_lean_certification")
    require(all(receipt[k] is False for k in IDENTITY_KEYS) and receipt["numerical_interval_kernel_proof"] is False,
            "lean_scope_mismatch")
    freeze = receipt["criterion_freeze"]
    require(freeze["commit"] == FREEZE and freeze["criterion"] == CRITERION and
            freeze["criterion_sha256"] == digest(HERE/CRITERION) and
            freeze["sources_sha256"] == digest(HERE/"sources.json") and receipt["source_packet_freeze"] == SOURCE_FREEZE,
            "lean_criterion_binding_mismatch")
    for row in (receipt["candidate"], receipt["direct_consumer"]):
        require(digest(ROOT/row["file"]) == row["sha256"], "lean_candidate_or_consumer_binding_mismatch")
    for name, sha in receipt["bindings"].items():
        require(digest(ROOT/name) == sha, "lean_source_binding_mismatch:"+name)
    focused = receipt["focused_verification"]
    require(focused["fresh_source_compilation"] is True and focused["trust_level"] == 0 and
            focused["warning_as_error"] is True and len(focused["commands"]) == 3 and
            all(row["exit_code"] == 0 for row in focused["commands"]) and
            "COLLECTED_RESPONSE_CERTIFIED" in focused["commands"][-1]["stdout"], "invalid_lean_compile_receipt")
    require(len(focused["lsp"]) == 3 and all(row["errors"] == row["warnings"] == 0 for row in focused["lsp"]),
            "invalid_lean_lsp_receipt")
    require(receipt["authorized_axioms"] == ["propext", "Classical.choice", "Quot.sound"], "unauthorized_lean_axioms")
    for name in ("SourceResponse.lean", "SourceResponseCertification.lean", "certification.json"):
        bindings[relative(HERE/name)] = digest(HERE/name)
    return receipt


class Formal:
    """Exact rational expressions; formal axes replace trigonometry, not source objects."""
    polynomial = None

    def __init__(self, numerator=0, denominator=None):
        if isinstance(numerator, complex):
            require(numerator.imag == 0, "nonreal_formal_constant")
            numerator = numerator.real
        self.n = self.polynomial.cast(numerator)
        self.d = self.polynomial(1) if denominator is None else self.polynomial.cast(denominator)
        require(bool(self.d.coefficients), "zero_formal_denominator")
        if not self.n.coefficients:
            self.d = self.polynomial(1)
        elif set(self.d.coefficients) == {()}:
            self.n /= self.d.coefficients[()]
            self.d = self.polynomial(1)

    @classmethod
    def cast(cls, x):
        return x if isinstance(x, cls) else cls(x)

    @classmethod
    def variable(cls, name):
        return cls(cls.polynomial.variable(name))

    def __add__(self, other):
        other = self.cast(other)
        if self.d.coefficients == other.d.coefficients:
            return type(self)(self.n+other.n, self.d)
        return type(self)(self.n*other.d+other.n*self.d, self.d*other.d)

    __radd__ = __add__

    def __neg__(self):
        return type(self)(-self.n, self.d)

    def __sub__(self, other):
        return self+-self.cast(other)

    def __rsub__(self, other):
        return self.cast(other)+-self

    def __mul__(self, other):
        other = self.cast(other)
        return type(self)(self.n*other.n, self.d*other.d)

    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self.cast(other)
        return type(self)(self.n*other.d, self.d*other.n)

    def __rtruediv__(self, other):
        return self.cast(other)/self

    def __pow__(self, power):
        require(isinstance(power, int) and power >= 0, "unsupported_formal_power")
        result = type(self)(1)
        for _ in range(power):
            result *= self
        return result

    def square(self):
        return self*self

    def conjugate(self):
        return self

    @property
    def real(self):
        return self

    @property
    def imag(self):
        return 0

    def __float__(self):
        require(not (set(self.n.coefficients)-{()}) and set(self.d.coefficients) == {()}, "nonconstant_formal_float")
        return float(self.n.coefficients.get((), F(0))/self.d.coefficients[()])

    def __abs__(self):
        if not (set(self.n.coefficients)-{()}):
            return abs(self.n.coefficients.get((), F(0))/self.d.coefficients[()])
        expression = self
        class Norm:
            def __pow__(self, power):
                require(power == 2, "formal_norm_requires_square")
                return expression.square()
        return Norm()

    # These endpoints suppress only the symbolic sign/display branch. Actual signs are checked rationally.
    lo, hi = -1, 1

    def receipt(self):
        return self


def symbolic_source_identity(primary, independent):
    math_module, source = independent.helpers()
    Poly = math_module.Polynomial
    class Ring(Formal):
        polynomial = Poly
    var = Ring.variable
    state = {}
    source_object = object.__new__(primary.collection.OpticalSource)
    source_object.na = source_object.nb = 2
    source_object.f = [[[var(f"F_{p}_{i}_{j}") for j in range(2)] for i in range(2)] for p in range(2)]
    source_object.optics = [[[(var(f"t_{side}_{p}_{i}"), var(f"l_{side}_{p}_{i}")) for i in range(2)]
                            for p in range(2)] for side in range(2)]
    for ap, p, i, bp, j in itertools.product(range(2), repeat=5):
        state[(ap,p,i,bp,p,j)] = var("prep_"+str(p))*source_object.f[p][i][j]*source_object.optics[0][p][i][ap]*source_object.optics[1][p][j][bp]
    objects = source.density_objects(state)
    statistics = FunctionType(primary.collection.OpticalSource.statistics.__code__,
                             {**primary.collection.__dict__, "math": SimpleNamespace(fsum=lambda xs: sum(xs, Ring(0)))})
    source_object.statistics = MethodType(statistics, source_object)
    producer = FunctionType(primary.collection.OpticalSource.objects_from_preparation.__code__,
                            {**primary.collection.__dict__, "complex": Ring.cast})
    for h, v in ((F(1),F(0)), (F(0),F(1)), (F(3,5),F(4,5))):
        actual = producer(source_object, h, v)
        prepared = {key: Ring([h,v][key[1]])*source_object.f[key[1]][key[2]][key[5]]*
                    source_object.optics[0][key[1]][key[2]][key[0]]*
                    source_object.optics[1][key[4]][key[5]][key[3]] for key in state}
        expected = source.density_objects(prepared)
        for name in ("AB","A","B"):
            require(all(not (Ring.cast(x)-Ring.cast(y)).n.coefficients for a,b in zip(actual[name],expected[name]) for x,y in zip(a,b)),
                    "collection_objects_not_orthogonal_source_polynomial")
    def projector(name, derivative=False):
        s,c = var("s"+name),var("c"+name)
        return [[s,c],[c,-s]] if derivative else [[(1-c)/2,s/2],[s/2,(1+c)/2]]
    globals_ = {**primary.__dict__, "projector": projector}
    methods = {name:FunctionType(getattr(primary.Model,name).__code__,globals_) for name in ("rates","score","derivative")}
    model = type("FormalNativeMatrix",(),methods)()
    model.objects = objects
    model.Q, model.uA, model.uB, model.bA, model.bB, model.lam = map(var,("Q","uA","uB","bgA","bgB","lambda"))
    score = model.score(["a0","a1","b0","b1"])
    require(score.d.coefficients == {():F(1)}, "unexpected_raw_CH_denominator")
    def differentiate(poly, name):
        coefficients = {}
        for monomial, value in poly.coefficients.items():
            powers = dict(monomial); exponent = powers.get(name,0)
            if exponent:
                powers[name] -= 1
                if not powers[name]: del powers[name]
                key = tuple(sorted(powers.items()))
                coefficients[key] = coefficients.get(key,F(0))+value*exponent
        return Poly(coefficients=coefficients)
    T = objects["AB"][0][0]+objects["AB"][3][3]
    K = objects["AB"][0][3]
    DA,DB = objects["A"][1][1]-objects["A"][0][0],objects["B"][1][1]-objects["B"][0][0]
    for side,own,other in (("alice","a1",("b0","b1")),("bob","b1",("a0","a1"))):
        s,c = var("s"+own),var("c"+own)
        dc,ds = var("c"+other[0])-var("c"+other[1]),var("s"+other[0])-var("s"+other[1])
        derived = Ring(differentiate(score.n,"s"+own))*2*c-Ring(differentiate(score.n,"c"+own))*2*s
        matrix = model.derivative(["a0","a1","b0","b1"],side)
        factored = model.Q*model.uA*model.uB/2*(-(T+model.lam*model.Q*DA*DB)*s*dc+2*K*c*ds)
        require(not (matrix-derived).n.coefficients and not (matrix-factored).n.coefficients,
                "actual_matrix_derivative_not_source_CH_identity")
        box = {name:name for name in ("a0","a1","b0","b1")}
        box.update(r_col=var("r_col"),gamma=var("gamma"),t=var("t"))
        function = FunctionType(primary.response_interval.__code__,
            {**primary.__dict__, "arithmetic":SimpleNamespace(sin_cos=lambda name,pi,terms:(var("s"+name),var("c"+name)))})
        normalized = function(box,side,None,None)["normalized_per_radian"]
        chi = 2*box["r_col"]/(1+box["r_col"].square())
        environment = {"s":s,"c":c,"dc":dc,"ds":ds,"t":box["t"],"gamma":box["gamma"],"chi_col":chi}
        generated = Ring(0)
        for monomial, coefficient in independent.generated_native_response()[0].coefficients.items():
            term = Ring(coefficient)
            for name, exponent in monomial: term *= environment[name]**exponent
            generated += term
        require(not (normalized-generated).n.coefficients, "interval_response_not_source_normalization_identity")
    return {"actual_collection_objects_equal_orthogonal_full_source":True,
            "actual_raw_CH_differentiation_equals_both_matrix_derivatives":True,
            "both_matrix_derivatives_equal_generated_T_K_DA_DB_coefficients":True,
            "primary_normalization_equals_independent_generated_source_polynomial":True,
            "method":"exact sparse polynomial numerator identities; actual source/statistics/objects, orthogonal partial traces and primary CH/derivative function bodies",
            "symbolic_scope":"finite real two-bin source and local columns; preparation quadratics checked on three spanning normalized preparations; complex frozen controls checked by full amplitudes"}


def bounds(row):
    lo,hi = F(row["exact_lower"]),F(row["exact_upper"])
    require(lo <= hi, "reversed_reported_interval")
    return lo,hi


def contains(row, value):
    require(isinstance(value,(int,float)) and not isinstance(value,bool) and math.isfinite(value), "nonfinite_source_readout")
    lo,hi = bounds(row)
    return lo <= F(value) <= hi


def validate_cases(primary, independent):
    require(tuple(c["case"] for c in primary["cases"]) == tuple(c["case"] for c in independent["cases"]) == CASES,
            "incomplete_continuous_cases")
    results = []
    for main,own in zip(primary["cases"],independent["cases"]):
        require(main["box"].keys() == own["box"].keys() and
                all(bounds(main["box"][k]) == bounds(own["box"][k]) for k in main["box"]), "continuous_domain_mismatch")
        require(main["paired_update"]["path_box"].keys() == own["paired_path_box"].keys() and
                all(bounds(main["paired_update"]["path_box"][k]) == bounds(own["paired_path_box"][k]) for k in main["box"]),
                "paired_update_source_or_domain_reset")
        for record,is_primary in ((main,True),(own,False)):
            response = record["responses"]
            name = "normalized_per_radian" if is_primary else "normalized"
            gain = record["paired_update"]["normalized_CH_improvement"] if is_primary else record["paired_normalized_improvement"]
            require(bounds(response["alice"][name])[1] < 0 < bounds(response["bob"][name])[0] and bounds(gain)[0] > 0,
                    "continuous_response_or_update_not_certified")
            require(response["alice"]["sign"] == "negative" and response["bob"]["sign"] == "positive" and
                    all(row["stationarity_excluded"] is True for row in response.values()) and record["status"] == "CERTIFIED",
                    "response_verdict_mismatch")
        for key in ("r_col","gamma","t"):
            require(bounds(main["box"][key]) == bounds(main["paired_update"]["path_box"][key]), "paired_update_source_or_domain_reset")
        results.append({"case":main["case"],"status":"CERTIFIED",
                        "primary_gain_lower":main["paired_update"]["normalized_CH_improvement"]["exact_lower"],
                        "independent_gain_lower":own["paired_normalized_improvement"]["exact_lower"],
                        "normalization":NORMALIZATION,"starting_source_retained":True})
    return results


def compare_source_controls(primary, independent, config):
    key = lambda row:(row["fixture"],row["r_src"],row["phase_pi"],row["lambda"],tuple(row["angles_deg"]))
    expected = set(itertools.product(config["controls"]["fixtures"],config["controls"]["r_src"],
                                    config["controls"]["phase_pi"],config["controls"]["lambda"],
                                    map(tuple,config["controls"]["angles_deg"])))
    main_rows,own_rows = primary["source_controls"]["rows"],independent["source_controls"]["rows"]
    a,b = {key(row):row for row in main_rows},{key(row):row for row in own_rows}
    require(len(main_rows) == len(own_rows) == len(expected) == 32 and a.keys() == b.keys() == expected,
            "source_control_coverage_mismatch")
    probability,derivative = (float(F(config["controls"][k])) for k in ("probability_tolerance","derivative_tolerance"))
    worst = {"CH":0.,"derivative":0.,"update":0.,"source":0.}
    points = []
    for name,main in a.items():
        own = b[name]; stats = own["source_statistics"]
        worst["CH"] = max(worst["CH"],abs(main["CH"]-own["CH"]))
        worst["update"] = max(worst["update"],abs(main["paired_CH_improvement"]-own["paired_improvement"]))
        worst["source"] = max(worst["source"],abs(main["trace_joint"]-stats["T"]),
                              abs(main["real_joint_coherence"]-2*stats["K"]),
                              abs(main["single_contrasts"]["A"]-stats["DA"]),abs(main["single_contrasts"]["B"]-stats["DB"]))
        for side in ("alice","bob"):
            worst["derivative"] = max(worst["derivative"],abs(main["derivatives_per_radian"][side]-own["derivatives"][side]["amplitude_per_radian"]))
        require(abs(stats["norm"]-1) <= probability and 0 < stats["T"] <= stats["TA"]+probability and
                stats["T"] <= stats["TB"]+probability and abs(stats["DA"]) <= stats["TA"]+probability and
                abs(stats["DB"]) <= stats["TB"]+probability, "actual_source_bound_control_failed")
        if own["r_src"] == "276/961" and own["phase_pi"] == "0" and own["angles_deg"] == config["angles_deg"]:
            case = 0 if own["lambda"] == "0" else 1
            scale = math.prod(float(F(config["controls"][k])) for k in ("Q","uA","uB"))*stats["T"]
            require(scale > 0, "zero_native_normalization")
            normalized = {side:own["derivatives"][side]["amplitude_per_radian"]/scale for side in ("alice","bob")}
            gain = own["paired_improvement"]/scale
            require(all(contains(primary["cases"][case]["responses"][side]["normalized_per_radian"],value) and
                        contains(independent["cases"][case]["responses"][side]["normalized"],value) for side,value in normalized.items()) and
                    contains(primary["cases"][case]["paired_update"]["normalized_CH_improvement"],gain) and
                    contains(independent["cases"][case]["paired_normalized_improvement"],gain), "native_source_readout_outside_enclosures")
            points.append({"fixture":own["fixture"],"case":CASES[case],"normalized_derivatives":normalized,
                           "normalized_paired_gain":gain,"inside_both":True,
                           "scope":"synthetic source point in the mathematical box; experimental calibration identity remains unassigned"})
    require(worst["CH"] <= probability and worst["update"] <= probability and worst["source"] <= probability and
            worst["derivative"] <= derivative and len(points) == 4, "independent_native_source_disagreement")
    require(len(primary["source_controls"]["coordinate_endpoints"]) == len(independent["source_controls"]["coordinate_endpoints"]) == 4,
            "coordinate_endpoint_coverage_mismatch")
    return {"rows":32,"worst_deltas":worst,"native_enclosure_points":points}


@lru_cache(maxsize=4)
def recompute(fingerprint):
    primary,independent = implementation("response"),implementation("independent_response")
    config,_ = scientific_inputs()
    require(primary.load_frozen()[0] == independent.load_frozen() == config, "implementation_input_mismatch")
    main = primary.compute()
    cases = [independent.continuous_result(config,lam) for lam in (0,1)]
    controls = independent.source_controls(config)
    budgets = independent.budget_receipt(config)
    symbolic = symbolic_source_identity(primary,independent)
    return primary,independent,main,cases,controls,budgets,symbolic


def assess(report_dir=None, *, enabled=True):
    base = {"schema":SCHEMA,"version":VERSION,"evidence_valid":False,
            **{key:False for key in IDENTITY_KEYS}}
    if not enabled:
        return {**base,"status":"disabled_by_override"}
    directory = HERE if report_dir is None else Path(report_dir)
    try:
        main_hash,own_hash = digest(directory/PRIMARY),digest(directory/INDEPENDENT)
        main,own = (json.loads((directory/name).read_text()) for name in (PRIMARY,INDEPENDENT))
        config,sources = scientific_inputs()
        certification(sources)
        require(main["schema"] == "p23-collected-response-primary/v1" and own["schema"] == "p23-collected-response-independent/v1" and
                main["version"] == own["version"] == VERSION, "response_schema_or_revision_mismatch")
        require(all(main[k] is False and own[k] is False for k in IDENTITY_KEYS) and
                main["actual_final_NIST_calibration_bound"] is False and own["claim_is_conditional"] is True,
                "research_receipt_cannot_admit_production")
        require(main["other_implementation_output_used_as_input"] is False and own["other_implementation_output_used_as_input"] is False and
                main["bell_event_files_read"] == own["bell_event_files_read"] == 0, "invalid_computation_input_scope")
        psource = {name:sha for name,sha in sources.items() if name not in
                   {relative(HERE/x) for x in ("SourceResponse.lean","SourceResponseCertification.lean","certification.json")}}
        psource.update({relative(HERE/"response.py"):digest(HERE/"response.py"),
                        relative(HERE.parent/"response/response.py"):digest(HERE.parent/"response/response.py")})
        require(main["bindings"] == psource, "primary_source_binding_mismatch")
        isource = {k:v for k,v in psource.items() if k not in
                   (relative(HERE/"response.py"),relative(HERE.parent/"response/response.py"))}
        isource.update({relative(HERE/"independent_response.py"):digest(HERE/"independent_response.py"),
                       relative(HERE.parent/"response/independent_response.py"):digest(HERE.parent/"response/independent_response.py"),
                       relative(HERE/PRIMARY):main_hash})
        require(own["bindings"] == isource, "independent_source_binding_mismatch")
        fingerprint = tuple(sorted((name,sha) for name,sha in {**sources,**psource,**isource}.items()
                                   if name != relative(HERE/PRIMARY)))
        p,i,expected,cases,controls,budgets,symbolic = recompute(fingerprint)
        require(same_structure(main,expected), "primary_recomputation_mismatch")
        require(own["criterion_freeze"] == i.criterion_freeze(), "independent_freeze_mismatch")
        require(same_structure(own["cases"],cases), "independent_interval_recomputation_mismatch")
        require(same_structure(own["source_controls"],controls) and controls["passed"] is True,
                "independent_source_control_recomputation_mismatch")
        require(same_structure(own["budgets"],budgets) and budgets["public_q_identity_assigned"] is False and
                budgets["gamma_and_r_col_calibration_identity_assigned"] is False, "independent_calibration_budget_mismatch")
        require(same_structure(own["symbolic_source_certificate"],i.generated_native_response()[1]), "independent_source_polynomial_mismatch")
        require(own["calculation_implementation"]["scientific_ast_sha256"] == i.scientific_digest() == i.SCIENCE_AST_SHA and
                own["calculation_implementation"]["primary_code_or_output_used_as_input"] is False,
                "independent_calculation_provenance_mismatch")
        require(main["normalized_convention"] == NORMALIZATION and
                own["comparison"]["normalization_agrees"] == "dCH/(Q uA uB trace(OmegaAB)); per radian" and
                own["comparison"]["source_coherence_convention"] ==
                "primary real_joint_coherence=2 Re(OmegaAB[HH,VV]); independent source_statistics.K=Re(OmegaAB[HH,VV])",
                "comparison_unit_metadata_mismatch")
        require(own["comparison"]["primary_sha256"] == main_hash and
                own["comparison"]["primary_bindings"] == main["bindings"], "comparison_binding_mismatch")
        continuous = validate_cases(main,own)
        source_controls = compare_source_controls(main,own,config)
        verdict = "CERTIFIED" if all(c["status"] == "CERTIFIED" for c in cases) and controls["passed"] and budgets["all_budgets_covered"] else "NOT_CERTIFIED"
        require(main["status"] == own["status"] == verdict == "CERTIFIED", "incorrect_response_verdict")
        require(own["comparison"]["passed"] is True and all(own["comparison"][k] is True for k in
                ("source_bindings_agree","freeze_version_agree","conditional_scope_agrees")), "invalid_posthoc_comparison")
        require(tuple(row["case"] for row in own["comparison"]["cases"]) == CASES and
                all(row["passed"] is True for row in own["comparison"]["cases"]) and
                type(own["comparison"]["source_control_rows_compared"]) is int and
                own["comparison"]["source_control_rows_compared"] == 32 and
                len(own["comparison"]["actual_native_enclosure_points"]) == 4 and
                all(row["derivatives_inside_both"] is True and row["gain_inside_both"] is True
                    for row in own["comparison"]["actual_native_enclosure_points"]), "incomplete_posthoc_comparison")
        require(digest(directory/PRIMARY) == main_hash and digest(directory/INDEPENDENT) == own_hash and
                all(digest(ROOT/name) == sha for name,sha in {**sources,**psource,**isource}.items() if name != relative(HERE/PRIMARY)),
                "evidence_changed_during_verification")
        return {**base,"status":"verified","evidence_valid":True,"criterion_freeze":p.load_frozen()[1],
                "bindings":{**sources,**psource,**isource,relative(HERE/"verify.py"):digest(HERE/"verify.py"),
                            "response.json":main_hash,"independent_response.json":own_hash},
                "lean_candidate_certified":True,"symbolic_source_identity":symbolic,"continuous_cases":continuous,
                "native_source_controls_recomputed":source_controls,"normalized_convention":NORMALIZATION,
                "calibration_scope":"S1-S5, same preparation and unscreened/background-subtracted collection calibration; Gamma, plane and preparation identity remain unassigned",
                "q_identity_budgets":budgets,"scope":main["scope"],
                "verification_role":"fresh exact-rational numeric consumers linked to separately certified source response; numerical signs are not Lean kernel claims"}
    except FileNotFoundError as error:
        return {**base,"status":"missing_collected_response_evidence","reason":str(error)}
    except (ValueError,KeyError,TypeError,IndexError,AttributeError,ArithmeticError,ImportError,OSError,subprocess.SubprocessError) as error:
        return {**base,"status":"invalid_collected_response_evidence","reason":str(error)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check-only",action="store_true")
    parser.add_argument("--directory",type=Path)
    parser.add_argument("--disabled",action="store_true")
    args = parser.parse_args()
    result = assess(args.directory,enabled=not args.disabled)
    print(json.dumps(result,indent=2,allow_nan=False))
    return 0 if result["status"] == "verified" else 1


if __name__ == "__main__":
    raise SystemExit(main())
