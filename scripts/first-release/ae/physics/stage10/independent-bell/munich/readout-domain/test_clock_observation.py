import unittest
from types import SimpleNamespace
from dataclasses import replace

import clock_observation as code
import clock_observation_independent as independent
from history_feed import RecordHistory


def row(n, time, outcome="0", comment=" "):
    return (n, time, "0", outcome, "opaque-QRNG-id", "0", "no", comment, str(n) * 64)


class ClockObservationTests(unittest.TestCase):
    def test_exact_units_context_and_next_address(self):
        history = RecordHistory("synthetic", "local1", (row(1, "0.1"), row(2, "2000.3", "1")), frozenset((1, 2)))
        values = tuple(code.observations(history))
        self.assertEqual(values[0][-1], "10001/5")
        self.assertEqual(values[0][0][2:5], (1, "1" * 64, 2))
        self.assertEqual(values[0][2][1], "1")
        self.assertEqual(values[1][-2], "right_censored")
        result = code.summarize(history)
        self.assertEqual(result, independent.summarize(history.run, history.role, history.observations, history.paired_rows))
        self.assertEqual(sum(group["records"] for group in result["groups"]), 2)
        self.assertEqual(result["groups"][0]["cdf_counts"][3], 0)

    def test_unpaired_and_maintenance_are_not_removed(self):
        history = RecordHistory("synthetic", "local1", (row(1, "0"), row(2, "100", comment="Maintenance"), row(3, "300")), frozenset((1, 3)))
        values = tuple(code.observations(history))
        self.assertEqual(len(values), 3)
        self.assertEqual(values[0][0][4], 2)
        self.assertFalse(values[0][2][3])
        self.assertEqual(values[0][2][-1], "Maintenance")

    def test_clock_anomalies_and_censoring_remain_visible(self):
        history = RecordHistory("synthetic", "local2", (row(1, "10"), row(2, "10"), row(3, "5"), row(4, "not-a-time")), frozenset())
        statuses = [item[-2] for item in code.observations(history)]
        self.assertEqual(statuses, ["zero_clock_retained", "negative_clock_retained", "invalid_clock_retained", "right_censored"])
        self.assertEqual(code.summarize(history)["records"], 4)
        self.assertEqual(code.summarize(history), independent.summarize(history.run, history.role, history.observations, history.paired_rows))

    def test_selection_override_does_not_change_next_record(self):
        history = RecordHistory("synthetic", "local1", (row(1, "1"), row(2, "2"), row(3, "3")), frozenset((1, 3)))
        changed = replace(history, paired_rows=frozenset((1, 2, 3)))
        self.assertEqual([item[0] for item in code.observations(history)], [item[0] for item in code.observations(changed)])

    def test_same_gap_and_cem_token_does_not_supply_loss_label(self):
        history = RecordHistory("synthetic", "local1", (row(1, "0"), row(2, "30000")), frozenset((1, 2)))
        sample = next(code.observations(history))
        self.assertEqual(sample[-1], "30000")
        self.assertNotIn("loss", code.summarize(history))
        self.assertNotIn("ionized", code.summarize(history))

    def test_pair_address_not_sorted_membership_selects_clock(self):
        a = RecordHistory("synthetic", "local1", (row(1, "0"), row(2, "100"), row(3, "400")), frozenset((1, 2)))
        b = RecordHistory("synthetic", "local2", (row(1, "0"), row(2, "20"), row(3, "30")), frozenset((1, 2)))
        trial = SimpleNamespace(row=1, row_a=0, row_b=1, h=0, a=0, b=0, x=0, y=1)
        admitted = SimpleNamespace(trials=(trial,), audit={"admissible_row_offset_pairs": [[1, 1]]}, token_dictionaries={})
        result = code.pair_summary(a, b, admitted)
        self.assertEqual(result, independent.pair_summary("synthetic", a.observations, b.observations,
                                                         a.paired_rows, b.paired_rows, admitted))
        self.assertEqual(result["cells"][0]["local1_cdf_counts"][0], 1)
        self.assertEqual(result["cells"][0]["local2_cdf_counts"][0], 1)
        changed = SimpleNamespace(**dict(vars(trial), row_b=0))
        self.assertNotEqual(result["pair_clock_observations_sha256"],
                            code.pair_summary(a, b, SimpleNamespace(**dict(vars(admitted), trials=(changed,))))["pair_clock_observations_sha256"])


if __name__ == "__main__":
    unittest.main()
