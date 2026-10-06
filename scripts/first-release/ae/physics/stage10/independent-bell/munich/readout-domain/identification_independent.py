"""Independent source fibers and necessary projections of the frozen parent CS.

Only frozen primitive and receipt inputs are read.  The original 8D source
contractor and integer arithmetic are reused; identification formulas, event
archives, records, optimizers and primary endpoint numerics are not imported.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import itertools
from pathlib import Path

import independent as source


BASE, ROOT = source.BASE, source.ROOT
VERSION = "stage10-munich-readout-id0001"
SCHEMA = "stage10-munich-readout-identification-independent/v1"
PRIMARY_SCHEMA = "stage10-munich-readout-identification-primary/v1"
THRESHOLD = Fraction(240)
LOW, HIGH = Fraction(19, 20), Fraction(21, 20)
ALTERNATIVES = (("isotropic", HIGH, HIGH), ("anisotropic", HIGH, LOW))
PRIMARY_FILES = ("criterion-id0001.md", "identification.py", "test_identification.py", "identify.py",
                 "identification_independent.py", "test_identification_independent.py",
                 "IdentificationCertification.lean", "identification_certify.py",
                 "test_identification_certify.py", "identification-certification-first.json")
PARENT_FILES = ("primitive-witness-c0002.json", "primary-first-c0002.json", "independent-first-c0002.json",
                "verification.json", "criterion.md")
require, canonical, rational = source.require, source.canonical, source.rational


def encode_point(point):
    return {side: [{key: str(getattr(effect, key)) for key in ("mu", "u", "z")} for effect in point[side]]
            for side in ("alice", "bob")}


def recover_observables(table):
    require(set(table) == set(itertools.product((0, 1), repeat=5)), "complete_32_source_probabilities")
    mu = {side: [None, None] for side in ("alice", "bob")}
    correlation = {}
    for h, a, b in itertools.product((0, 1), repeat=3):
        require(sum(table[h, a, b, x, y] for x, y in itertools.product((0, 1), repeat=2)) == 1,
                "source_distribution_normalization")
        first = 2 * sum(table[h, a, b, 0, y] for y in (0, 1)) - 1
        second = 2 * sum(table[h, a, b, x, 0] for x in (0, 1)) - 1
        for side, setting, value in (("alice", a, first), ("bob", b, second)):
            require(mu[side][setting] is None or mu[side][setting] == value, "shared_local_marginal_changed")
            mu[side][setting] = value
        correlation[h, a, b] = sum((1 - 2 * x) * (1 - 2 * y) * table[h, a, b, x, y]
                                  for x, y in itertools.product((0, 1), repeat=2))
    x_matrix, z_matrix = [], []
    for a in (0, 1):
        x_matrix.append([(correlation[1, a, b] - correlation[0, a, b]) / 2 for b in (0, 1)])
        z_matrix.append([mu["alice"][a] * mu["bob"][b] -
                         (correlation[0, a, b] + correlation[1, a, b]) / 2 for b in (0, 1)])
    return {"alice_bias": list(map(str, mu["alice"])), "bob_bias": list(map(str, mu["bob"])),
            "X": [[str(value) for value in row] for row in x_matrix],
            "Z": [[str(value) for value in row] for row in z_matrix]}


def scaled_point(point, s, t):
    s, t = rational(s), rational(t)
    require(s != 0 and t != 0, "nonzero_source_scales_required")
    return {side: tuple(source.Effect(effect.mu,
                                     effect.u * s if side == "alice" else effect.u / s,
                                     effect.z * t if side == "alice" else effect.z / t)
                        for effect in point[side]) for side in ("alice", "bob")}


def check_alternative(point, proposed, s, t):
    alternative = source.primitive(proposed)
    expected = scaled_point(point, s, t)
    require(alternative == expected, "alternative_not_the_declared_source_scale")
    original_q, alternative_q = source.born_table(point), source.born_table(alternative)
    require(original_q == alternative_q, "full_8D_Born_law_changed")
    changes, changed = [], []
    for side in ("alice", "bob"):
        for setting, (old, new) in enumerate(zip(point[side], alternative[side])):
            old_norm, new_norm = old.u ** 2 + old.z ** 2, new.u ** 2 + new.z ** 2
            changes.append({"side": side, "setting": setting,
                            "original_gain_squared": str(old_norm), "alternative_gain_squared": str(new_norm)})
            if old_norm != new_norm:
                changed.append([side, setting])
    return {"gain_changes": changes, "changed_canonical_channel_settings": changed,
            "canonical_error_change_reason": "mu fixed; each error is (1 plus_or_minus mu minus sqrt(gain_squared))/2",
            "probabilities_compared": 32, "all_8D_generated_probabilities_unchanged": True,
            "same_statistical_factors_for_all_original_prefixes": True}


def rectangle(point, low=LOW, high=HIGH):
    low, high = rational(low), rational(high)
    require(0 < low < high, "positive_continuous_rectangle")
    constraints = []
    for side in ("alice", "bob"):
        for setting, effect in enumerate(point[side]):
            capacity = (1 - abs(effect.mu)) ** 2
            norm = effect.u ** 2 + effect.z ** 2
            largest = norm * high ** 2 if side == "alice" else norm / low ** 2
            require(largest <= capacity, "continuous_rectangle_exits_cone")
            constraints.append({"side": side, "setting": setting, "maximum_norm_squared": str(largest),
                                "capacity_squared": str(capacity), "slack": str(capacity - largest)})
    return {"s": [str(low), str(high)], "t": [str(low), str(high)], "constraints": constraints,
            "entire_continuous_rectangle_legal": True, "finite_samples_used_as_coverage": False}


def regular_description(point, quotient):
    require(rational(quotient["X"][0][0]) != 0 and rational(quotient["Z"][0][0]) != 0,
            "regular_X00_Z00_anchor_required")
    constraints = []
    for side in ("alice", "bob"):
        for setting, effect in enumerate(point[side]):
            constraints.append({"side": side, "setting": setting, "u_squared": str(effect.u ** 2),
                                "z_squared": str(effect.z ** 2), "capacity_squared": str((1 - abs(effect.mu)) ** 2),
                                "kind": "u2*S+z2*T<=capacity2" if side == "alice" else "u2/S+z2/T<=capacity2"})
    return {"regular_anchor": "X00_and_Z00_nonzero", "constraints": constraints,
            "squared_coordinates": {"S": "s^2>0", "T": "t^2>0"},
            "sign_branches": [[s, t] for s, t in itertools.product((-1, 1), repeat=2)],
            "continuous_fiber": "all_nonzero_s_t_satisfying_all_four_source_cones",
            "isotropic_subfamily_preserves_all_axes": True,
            "fixed_generated_law_is_actual_empirical_probability": False}


def own_setting_counts(rows):
    require(type(rows) is list and len(rows) == 8, "complete_parent_count_inventory")
    result = {side: [[0, 0], [0, 0]] for side in ("alice", "bob")}
    seen = set()
    for row in rows:
        require(type(row) is dict and set(row) == {"h", "a", "b", "counts"}, "parent_count_row_shape")
        h, a, b = (row[key] for key in ("h", "a", "b"))
        require(all(type(n) is int and n in (0, 1) for n in (h, a, b)) and (h, a, b) not in seen,
                "parent_context_identity")
        seen.add((h, a, b))
        counts = row["counts"]
        require(type(counts) is list and len(counts) == 4 and all(type(n) is int and n >= 0 for n in counts),
                "parent_natural_counts")
        for outcome, n in enumerate(counts):
            x, y = divmod(outcome, 2)
            result["alice"][a][x] += n
            result["bob"][b][y] += n
    require(seen == set(itertools.product((0, 1), repeat=3)), "parent_context_coverage")
    return result


class Profile:
    """Integer log bounds for a necessary parent-CS marginal projection."""
    def __init__(self, counts, setting, bits=240):
        require(type(setting) is int and setting in (0, 1) and type(counts) is list and len(counts) == 2,
                "two_setting_profile")
        require(all(type(row) is list and len(row) == 2 and all(type(n) is int and n >= 0 for n in row)
                    for row in counts), "profile_natural_counts")
        self.counts, self.setting = counts, setting
        self.own, self.other = counts[setting], counts[1 - setting]
        require(sum(self.own) > 0, "own_setting_empty")
        self.arithmetic = source.Arithmetic(bits)
        pooled = [counts[0][x] + counts[1][x] for x in (0, 1)]
        numerator = self.arithmetic.predictor_log(pooled, 2)
        total_other = sum(self.other)
        self.other_mle = Fraction(self.other[0], total_other) if total_other else Fraction(1, 2)
        other_log = self.log_likelihood(self.other, self.other_mle)
        require(other_log is not None, "other_MLE_support")
        self.constant = numerator - other_log
        self.mle = Fraction(self.own[0], sum(self.own))
        self.threshold = self.arithmetic.log(THRESHOLD)

    def log_likelihood(self, counts, p):
        p = rational(p)
        require(0 <= p <= 1, "probability_coordinate")
        if (counts[0] and p == 0) or (counts[1] and p == 1):
            return None
        answer = source.Bounds(0, 0)
        for n, probability in zip(counts, (p, 1 - p)):
            if n:
                answer += self.arithmetic.log(probability).times(n)
        return answer

    def at(self, p):
        likelihood = self.log_likelihood(self.own, p)
        return None if likelihood is None else self.constant - likelihood

    def derivative_sign_numerator(self, p):
        p = rational(p)
        require(0 < p < 1, "interior_derivative")
        return sum(self.own) * p - self.own[0]

    def certify(self, low, high, parent_mu=None):
        low, high = rational(low), rational(high)
        require(0 <= low < self.mle < high <= 1, "outer_interval_straddles_unique_MLE")
        left, right, center = self.at(low), self.at(high), self.at(self.mle)
        require(center is not None and center.hi < self.threshold.lo, "MLE_not_inside_profile_set")
        require(left is None or left.lo >= self.threshold.hi, "left_endpoint_not_excluded")
        require(right is None or right.lo >= self.threshold.hi, "right_endpoint_not_excluded")
        # On either outside interval, this exact numerator fixes the derivative sign.
        require(sum(self.own) * low - self.own[0] <= 0 and
                sum(self.own) * high - self.own[0] >= 0, "outside_monotonicity")
        if parent_mu is not None:
            parent_p = (1 + rational(parent_mu)) / 2
            own_point = self.at(parent_p)
            require(low < parent_p < high and own_point is not None and own_point.hi < self.threshold.lo,
                    "parent_point_not_in_necessary_profile_set")
        encode = lambda bound: {"infinite": True} if bound is None else self.arithmetic.record(bound)
        return {"p_mle": str(self.mle), "p_outer_interval": [str(low), str(high)],
                "mu_outer_interval": [str(2 * low - 1), str(2 * high - 1)],
                "left_log_profile": encode(left), "right_log_profile": encode(right),
                "mle_log_profile": encode(center), "component_threshold": "240",
                "entire_outside_intervals_excluded": True, "profile_convexity_from_exact_derivative": True,
                "other_setting_MLE": {"p": str(self.other_mle), "counts": self.other},
                "new_confidence_budget_spent": False, "kind": "necessary_outer_projection_of_entire_parent_confidence_set"}


def certify_projection(counts, setting, interval, parent_mu):
    require(type(interval) is list and len(interval) == 2, "outer_interval_shape")
    reason = None
    for bits in (240, 320, 384):
        try:
            result = Profile(counts, setting, bits).certify(*interval, parent_mu=parent_mu)
            result["precision_bits"] = bits
            return result
        except ValueError as error:
            reason = error
    raise reason


def check_primary(primary, witness, parent_first):
    require(primary.get("schema") == PRIMARY_SCHEMA and primary.get("version") == VERSION,
            "identification_primary_identity")
    require(primary.get("status") == "generated_parameter_fibers_and_parent_confidence_projections",
            "identification_primary_not_complete")
    for field in ("new_confidence_budget_spent", "optimizer_run", "actual_hardware_uniquely_identified"):
        require(primary.get(field) is False, "identification_scope_promotion")
    require(primary.get("parent_confidence_budget") == "1/20" and
            type(primary.get("trial_event_files_read")) is int and primary["trial_event_files_read"] == 0,
            "identification_budget_or_event_scope")
    for value in (primary, witness, parent_first):
        require(type(value.get("runs")) is list and tuple(run.get("run") for run in value["runs"]) == source.RUNS,
                "complete_two_run_identity")
    results = []
    for reported, saved, counted in zip(primary["runs"], witness["runs"], parent_first["runs"]):
        require(canonical(reported["primitive"]) == canonical(saved["primitive"]), "parent_primitive_changed")
        point = source.primitive(saved["primitive"])
        table = source.born_table(point)
        quotient = recover_observables(table)
        require(canonical(reported["observable_quotient"]) == canonical(quotient), "observable_quotient_not_from_Born")
        require(canonical(reported["regular_fiber"]) == canonical(regular_description(point, quotient)),
                "complete_regular_fiber_descriptor_changed")
        continuous = rectangle(point)
        require(canonical(reported["continuous_legal_rectangle"]) == canonical(continuous), "rectangle_coverage_changed")
        alternatives = reported["equivalent_hardware"]
        require(type(alternatives) is list and len(alternatives) == 2, "alternative_inventory")
        alternative_results = []
        for proposed, (kind, s, t) in zip(alternatives, ALTERNATIVES):
            require(proposed["kind"] == kind and rational(proposed["s"]) == s and rational(proposed["t"]) == t,
                    "fixed_alternative_scale_changed")
            checked = check_alternative(point, proposed["primitive"], s, t)
            require(checked["changed_canonical_channel_settings"], "nonuniqueness_witness_does_not_change_gain")
            require(canonical(proposed["gain_changes"]) == canonical(checked["gain_changes"]), "gain_change_claim_changed")
            require(proposed["all_generated_probabilities_unchanged"] is True and
                    type(proposed["all_original_prefixes_inherited"]) is int and
                    proposed["all_original_prefixes_inherited"] == counted["trials"], "parent_prefix_inheritance_changed")
            alternative_results.append({"kind": kind, "s": str(s), "t": str(t), **checked})
        own = own_setting_counts(counted["four_outcomes"])
        require(canonical(reported["own_setting_counts"]) == canonical(own), "counts_not_from_parent_first")
        require(type(counted["trials"]) is int and counted["trials"] == sum(map(sum, own["alice"])) ==
                sum(map(sum, own["bob"])), "parent_trial_accounting")
        require(reported["parent_factor_sequence_sha256"] == counted["prefix_check"]["factor_sequence_sha256"],
                "parent_factor_identity_changed")
        envelopes = reported["bias_envelopes"]
        require(type(envelopes) is list and len(envelopes) == 4, "complete_bias_envelopes")
        checked_envelopes = []
        for supplied, (side, setting) in zip(envelopes, itertools.product(("alice", "bob"), (0, 1))):
            require(supplied["side"] == side and type(supplied["setting"]) is int and supplied["setting"] == setting,
                    "bias_projection_role")
            require(canonical(supplied["counts"]) == canonical(own[side]) and supplied["component_threshold"] == "240",
                    "bias_projection_input_or_threshold")
            require(supplied["kind"] == "necessary_outer_projection_of_entire_parent_confidence_set" and
                    supplied["new_confidence_budget_spent"] is False and
                    supplied["point_witness_used_as_confidence_bound"] is False, "bias_projection_scope")
            checked = certify_projection(own[side], setting, supplied["p_outer_interval"], point[side][setting].mu)
            require(supplied["p_mle"] == checked["p_mle"] and
                    canonical(supplied["mu_outer_interval"]) == canonical(checked["mu_outer_interval"]),
                    "bias_projection_exact_coordinates")
            checked_envelopes.append({"side": side, "setting": setting, "counts": own[side], **checked})
        results.append({"run": saved["run"], "observable_quotient": quotient, "regular_anchor_checked": True,
                        "continuous_legal_rectangle": continuous, "equivalent_hardware": alternative_results,
                        "bias_envelopes": checked_envelopes, "own_setting_counts": own,
                        "parent_factor_sequence_sha256": reported["parent_factor_sequence_sha256"]})
    return {"schema": SCHEMA, "version": VERSION, "status": "certified_source_fiber_and_parent_CS_projections",
            "evidence_valid": True, "runs": results, "parent_confidence_budget": "1/20",
            "source_probabilities_checked": 64, "alternative_probabilities_checked": 128,
            "bias_envelopes_checked": 8, "new_confidence_budget_spent": False,
            "trial_event_files_read": 0, "optimizer_run": False, "actual_hardware_uniquely_identified": False,
            "primary_endpoint_numerics_used": False, "complete_fiber_proof_supplied_by_finite_examples": False,
            "source_theorem_changed": False, "controller_advance": False}


def frozen_bindings(commit):
    names = (*PRIMARY_FILES, *PARENT_FILES, "independent.py", "source-certification-first.json",
             "likelihood_certify.py", "likelihood-certification-first.json", "LikelihoodCertification.lean",
             "criterion-c0002.md")
    lean = ROOT / "Lean/SaturationMonoid/PhysicsCore/Stage10/Bell"
    entries = []
    for path in [BASE / name for name in names] + [source.BORN_PATH, lean / "ReadoutLikelihood.lean",
                                                  lean / "ReadoutIdentification.lean"]:
        raw = source.frozen_bytes(path, commit)
        require(raw == source.frozen_bytes(path), "identification_source_not_at_execution_HEAD")
        entries.append({"path": str(path.relative_to(ROOT)), "sha256": source.digest(raw)})
    return entries


def primary_provenance(primary, bindings, freeze_commit):
    names = [str((BASE / name).relative_to(ROOT)) for name in (*PRIMARY_FILES, *PARENT_FILES)]
    inventory = {entry["path"]: entry for entry in bindings}
    require(canonical(primary["source_bindings"]) == canonical([inventory[name] for name in names]),
            "primary_scientific_binding_inventory_changed")
    require(primary["freeze_commit"] == freeze_commit, "primary_scientific_freeze_changed")
    require(primary["parent_certificate_sha256"] ==
            inventory[str((BASE / "verification.json").relative_to(ROOT))]["sha256"], "parent_certificate_changed")
    require(primary["identification_kernel_sha256"] ==
            inventory[str((BASE / "identification-certification-first.json").relative_to(ROOT))]["sha256"],
            "identification_kernel_receipt_changed")
    attempt_raw = source.frozen_bytes(BASE / "identification-attempt.json")
    require(primary["attempt_sha256"] == source.digest(attempt_raw), "primary_first_attempt_changed")
    attempt = source.strict_json(attempt_raw)
    require(attempt["version"] == VERSION and attempt["freeze_commit"] == freeze_commit and
            canonical(attempt["source_bindings"]) == canonical(primary["source_bindings"]) and
            type(attempt["event_files_read_at_reservation"]) is int and attempt["event_files_read_at_reservation"] == 0,
            "primary_attempt_scope_or_bindings_changed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--freeze-commit", required=True)
    parser.add_argument("--primary-receipt", type=Path, default=BASE / "identification-first.json")
    args = parser.parse_args()
    attempt = BASE / "identification-independent-attempt.json"
    first = BASE / "identification-independent-first.json"
    try:
        require(not attempt.exists() and not first.exists(), "identification_independent_first_already_reserved")
        provenance = source.execution_provenance(args.freeze_commit)
        bindings = frozen_bindings(provenance["freeze_commit"])
        root_raw = source.frozen_bytes(BASE / "identification-first.json")
        require(args.primary_receipt.read_bytes() == root_raw, "primary_override_changes_frozen_receipt")
        witness_raw = source.frozen_bytes(BASE / "primitive-witness-c0002.json")
        parent_raw = source.frozen_bytes(BASE / "primary-first-c0002.json")
        source.exclusive_json(attempt, {"schema": "stage10-munich-identification-independent-attempt/v1",
                                       "version": VERSION, "provenance": provenance, "source_bindings": bindings,
                                       "primary_receipt_sha256": source.digest(root_raw), "trial_event_files_read": 0})
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(canonical({"schema": SCHEMA, "status": "not_started", "reason": str(error)}))
        return 2
    try:
        primary = source.strict_json(root_raw)
        primary_provenance(primary, bindings, provenance["freeze_commit"])
        report = check_primary(primary, source.strict_json(witness_raw), source.strict_json(parent_raw))
    except Exception as error:
        report = {"schema": SCHEMA, "version": VERSION, "status": "execution_failed", "evidence_valid": False,
                  "reason": str(error), "error_type": type(error).__name__}
    report.update({"source_bindings": bindings, "provenance": provenance,
                   "primary_receipt_sha256": source.digest(root_raw), "parent_witness_sha256": source.digest(witness_raw),
                   "parent_primary_first_sha256": source.digest(parent_raw), "attempt_sha256": source.digest(attempt.read_bytes())})
    source.exclusive_json(first, report)
    print(canonical({"schema": SCHEMA, "status": report["status"], "evidence_valid": report["evidence_valid"]}))
    return 0 if report["evidence_valid"] is True else 1


if __name__ == "__main__":
    raise SystemExit(main())
