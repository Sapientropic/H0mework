"""Controls for frozen inverse-fiber and whole-confidence projection consumption."""
import copy
from fractions import Fraction
import itertools
import unittest

import identification as producer
import identification_independent as independent
import identify_verify as consumer
from model import Effect, Instrument, encode


def fixture():
    point = Instrument((Effect(0, "1/8", "3/4"), Effect(0, "3/4", "1/8")),
                       (Effect(0, "1/2", "1/2"), Effect(0, "-1/2", "1/2")))
    primitive = encode(point)
    rows = [{"h": h, "a": a, "b": b, "counts": [4, 4, 4, 4]}
            for h, a, b in itertools.product((0, 1), repeat=3)]
    own = producer.own_counts(rows)
    q = producer.quotient(point)
    p_runs, i_runs, w_runs, c_runs = [], [], [], []
    for run in consumer.parent.RUNS:
        alternatives, checked_alternatives = [], []
        for kind, s, t in independent.ALTERNATIVES:
            new = producer.scale(point, s, t)
            checked = independent.check_alternative(independent.source.primitive(primitive), encode(new), s, t)
            alternatives.append({"kind": kind, "s": str(s), "t": str(t), "primitive": encode(new),
                                 "gain_changes": checked["gain_changes"], "all_original_prefixes_inherited": 128})
            checked_alternatives.append({"kind": kind, **checked})
        envelopes, checked_envelopes = [], []
        for side, setting in itertools.product(("alice", "bob"), (0, 1)):
            first = producer.Profile(own[side], setting).bounds()
            checked = independent.Profile(own[side], setting).certify(*first["p_outer_interval"])
            envelopes.append({"side": side, **first})
            checked_envelopes.append({"side": side, "setting": setting, "counts": own[side], **checked})
        common = {"run": run, "observable_quotient": q, "own_setting_counts": own,
                  "continuous_legal_rectangle": producer.positive_rectangle(point),
                  "parent_factor_sequence_sha256": "f" * 64}
        p_runs.append({**common, "primitive": primitive, "regular_fiber": producer.fixed_law_fiber(point),
                       "equivalent_hardware": alternatives, "bias_envelopes": envelopes})
        i_runs.append({**common, "equivalent_hardware": checked_alternatives, "bias_envelopes": checked_envelopes})
        w_runs.append({"run": run, "primitive": primitive})
        c_runs.append({"run": run, "trials": 128, "four_outcomes": rows,
                       "prefix_check": {"factor_sequence_sha256": "f" * 64}})
    shared = {"version": consumer.VERSION, "parent_confidence_budget": "1/20", "new_confidence_budget_spent": False,
              "trial_event_files_read": 0, "optimizer_run": False, "actual_hardware_uniquely_identified": False}
    p = {**shared, "schema": "stage10-munich-readout-identification-primary/v1",
         "status": "generated_parameter_fibers_and_parent_confidence_projections", "runs": p_runs}
    i = {**shared, "schema": "stage10-munich-readout-identification-independent/v1", "evidence_valid": True,
         "status": "certified_source_fiber_and_parent_CS_projections", "runs": i_runs,
         "source_probabilities_checked": 64, "alternative_probabilities_checked": 128,
         "bias_envelopes_checked": 8, "primary_endpoint_numerics_used": False}
    return p, i, {"runs": w_runs}, {"runs": c_runs}


class IdentificationConsumerControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.base = fixture()

    def test_complete_dual_certificate_is_consumed(self):
        result = consumer.validate(*copy.deepcopy(self.base))
        self.assertEqual(len(result), 2)
        self.assertEqual(len(result[0]["bias_envelopes"]), 4)

    def test_unique_hardware_or_extra_budget_promotion_is_rejected(self):
        for field, value in (("actual_hardware_uniquely_identified", True), ("new_confidence_budget_spent", True),
                             ("parent_confidence_budget", "1/10"), ("trial_event_files_read", False)):
            p, i, w, c = copy.deepcopy(self.base)
            p[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                consumer.validate(p, i, w, c)

    def test_changed_quotient_or_cone_coverage_is_rejected(self):
        p, i, w, c = copy.deepcopy(self.base)
        i["observable_quotient"] = {}
        i["runs"][0]["observable_quotient"]["alice_bias"][0] = "1/5"
        with self.assertRaises(ValueError):
            consumer.validate(p, i, w, c)

    def test_fake_endpoint_inside_the_profile_is_rejected(self):
        p, i, w, c = copy.deepcopy(self.base)
        p["runs"][0]["bias_envelopes"][0]["lower_endpoint_log_e"] = {"lower": "0", "upper": "1"}
        with self.assertRaises(ValueError):
            consumer.validate(p, i, w, c)

    def test_incomplete_source_or_prefix_cross_is_rejected(self):
        for field, value in (("alternative_probabilities_checked", 127), ("bias_envelopes_checked", 7)):
            p, i, w, c = copy.deepcopy(self.base)
            i[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                consumer.validate(p, i, w, c)
        p, i, w, c = copy.deepcopy(self.base)
        c["runs"][0]["prefix_check"]["factor_sequence_sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            consumer.validate(p, i, w, c)


if __name__ == "__main__":
    unittest.main()
