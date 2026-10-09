"""Frozen evidence restores the same source; relocation cannot replace its data."""
from functools import lru_cache
from pathlib import Path
import json
import os
import sys
import tempfile
import unittest

import reissued_source_intake_rha0027 as code


@lru_cache(maxsize=1)
def evidence():
    return code.consume()


class ReissuedSourceIntakeControls(unittest.TestCase):
    def test_completed_local_curve_retains_the_paid_parent_and_issued_initial_factor(self):
        _, values, _ = evidence(); completed = code.completed_density_reports()
        self.assertEqual(len(completed), 1)
        for (side, factor), report in completed.items():
            source = values['prepared']
            row = next(item for item in source['source_issued_two_pump_factor_inlets'][side] if item['factor_id'] == factor)
            self.assertEqual(report['untrusted_trial']['complete_initial_matrix'],
                             row['source_issued_next_phase']['complete_initial_local_factor'])
            self.assertEqual(report['source_record']['Gaussian_source']['reference_local_parent'],
                             source['reference_local_parent'])
            self.assertEqual(report['source_interval_seconds'], ['0', '1/1000000000'])

    def test_current_source_restores_without_a_new_pump_residual_check(self):
        calls = []; previous = sys.getprofile()
        targets = (code.producer.programme._certify_phase.__code__, code.producer.programme._certify_shared_phase.__code__)
        def observe(frame, event, value):
            if event == 'call' and frame.f_code in targets: calls.append(frame.f_code.co_name)
        sys.setprofile(observe)
        try: source = code.restore_prepared()
        finally: sys.setprofile(previous)
        self.assertEqual(source.record(), evidence()[1]['prepared']); self.assertEqual(calls, [])

    def test_artifact_directory_override_preserves_the_same_source(self):
        receipt, original, _ = evidence()
        with tempfile.TemporaryDirectory() as directory:
            for binding in receipt['source_artifacts'].values():
                path = code.ROOT/binding['path']; os.link(path, Path(directory)/path.name)
            _, relocated, reports = code.consume(artifacts_directory=directory)
            self.assertEqual(relocated, original); self.assertEqual(len(reports), 20)

    def test_same_shape_replacement_is_rejected_before_source_cache_admission(self):
        receipt, _, _ = evidence()
        with tempfile.TemporaryDirectory() as directory:
            for role, binding in receipt['source_artifacts'].items():
                path = code.ROOT/binding['path']; target = Path(directory)/path.name
                if role == 'pumps': target.write_text(json.dumps({'schema': code.producer.programme.PHASE_SCHEMA+'/coimage'}))
                else: os.link(path, target)
            with self.assertRaisesRegex(ValueError, 'snapshot byte count|snapshot SHA'):
                code.consume(artifacts_directory=directory)


if __name__ == '__main__':
    unittest.main()
