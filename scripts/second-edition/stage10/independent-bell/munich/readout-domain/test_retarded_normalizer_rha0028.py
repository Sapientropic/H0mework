"""Completed evidence is reused; whole gate bounds keep their source and clock."""
from fractions import Fraction as Q
from pathlib import Path
from types import SimpleNamespace
import json
import os
import sys
import tempfile
import unittest

import completed_retarded_inlet_rha0028 as paid
import retarded_complete_receipt_normalizer_rha0028 as code
import retarded_normalizer_independent_rha0028 as independent
from test_retarded_gaussian_bsm_source import fixture as law_fixture


class CompletedInletControls(unittest.TestCase):
    def test_complete_inlet_restore_uses_no_new_local_residual(self):
        calls = []; before = sys.getprofile()
        targets = (paid.inlet.density.GaussianLocalDensitySource.certify.__code__,
                   paid.paid.producer.programme._certify_phase.__code__,
                   paid.paid.producer.programme._certify_shared_phase.__code__)
        def observe(frame, event, value):
            if event == 'call' and frame.f_code in targets: calls.append(frame.f_code.co_name)
        sys.setprofile(observe)
        try: source = paid.restore()
        finally: sys.setprofile(before)
        self.assertEqual(calls, [])
        self.assertEqual(source.record()['actual_retarded_local_cuts_seconds'], ['1/1000000000']*2)
        start = Q(source.record()['fixed_detector_gate_start_seconds'])
        zero = code.bounds(source, interval=(start, start))
        self.assertEqual(zero['whole_first_receipt_mass_interval'], ['0', '0'])
        self.assertFalse(zero['whole_first_receipt_strictly_positive'])

    def test_artifact_directory_override_preserves_complete_evidence(self):
        receipt = json.loads(paid.paid.frozen(paid.FIRST))
        with tempfile.TemporaryDirectory() as directory:
            for binding in (receipt['completed_producer_summary'], receipt['fresh_inlet']):
                path = paid.ROOT/binding['path']; os.link(path, Path(directory)/path.name)
            loaded, payload = paid.consume(artifacts_directory=directory)
            self.assertEqual(loaded, receipt)
            self.assertEqual(sum(map(len, payload['density_witnesses'])), 10)

    def test_lookalike_snapshot_cannot_supply_a_checked_inlet(self):
        receipt = json.loads(paid.paid.frozen(paid.FIRST))
        with tempfile.TemporaryDirectory() as directory:
            path = paid.ROOT/receipt['completed_producer_summary']['path']; os.link(path, Path(directory)/path.name)
            (Path(directory)/Path(receipt['fresh_inlet']['path']).name).write_text(json.dumps({'source_record': {}}))
            with self.assertRaisesRegex(ValueError, 'snapshot byte count'):
                paid.consume(artifacts_directory=directory)
        with self.assertRaisesRegex(ValueError, 'closed current source-issued'):
            code.bounds(SimpleNamespace())

    def test_independent_full_complex_source_BG_flow_matches_exact_subinstrument(self):
        law = law_fixture(); raw = law.record(); duration = Q(raw['gate_seconds'][1])-Q(raw['gate_seconds'][0])
        direct, price, count = independent.background_masses(raw, duration)
        original = code.empty.RetardedEmptyReceiptTimeMeasure(law).interval(*map(Q, raw['gate_seconds']))
        self.assertEqual(count, 45)
        for value, row in zip(direct, original['four_pattern_poststates']):
            self.assertGreater(value-price, 0)
            self.assertLessEqual(abs(value-Q(row['centre_mass'])), price+Q(row['whole_trace_norm_error']))
        zero, price, _ = independent.background_masses(raw, Q(0))
        self.assertEqual(zero, [Q(0)]*4); self.assertEqual(price, 0)

    def test_independent_operator_reader_preserves_nonhermitian_raising_and_jump_columns(self):
        value = independent.dipole.ComplexRadical(Q(1, 3), Q(1, 5))
        rows = [[1, 2, value.serialize()]]
        self.assertEqual(independent._operator(rows), {(1, 2): value})
        with self.assertRaisesRegex(ValueError, 'duplicate or out-of-range'):
            independent._operator(rows+rows)

    def test_incomplete_pattern_inventory_cannot_certify_a_whole_gate(self):
        law = law_fixture().record()
        lookalike = {'schema': 'stage10-complete-retarded-receipt-normalizer/rha0028',
            'source_record': {'retarded_detector_law': law}, 'receipt_interval_seconds': law['gate_seconds'],
            'invariant_empty_face': {'four_pattern_poststates': [{'pattern': p} for p in range(3)]},
            'four_pattern_mass_bounds': [{'pattern': p} for p in range(3)]}
        with self.assertRaisesRegex(ValueError, 'all four original receipt patterns'):
            independent.certify(lookalike)

    def test_exact_rational_bounds_serialize_as_outward_finite_dyadics(self):
        value = Q(1, 10**5000)
        lower, upper = map(Q, independent._interval_record(value, 2*value))
        self.assertLessEqual(lower, value); self.assertGreaterEqual(upper, 2*value)
        self.assertLessEqual(max(lower.denominator.bit_length(), upper.denominator.bit_length()), 193)
        self.assertEqual(independent._interval_record(Q(1, 8), Q(1, 4)), ['1/8', '1/4'])


if __name__ == '__main__':
    unittest.main()
