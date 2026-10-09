"""Reuse a checked curve without weakening its source, price or closure identity."""
import copy
from functools import lru_cache
from fractions import Fraction as Q
from pathlib import Path
import json
import sys
import unittest

import gaussian_local_density_source as code
import reference_local_phase_source as reference
from test_fourier_reference_local_programme_source import raw_plan


@lru_cache(maxsize=1)
def fixture():
    root = Path(__file__).resolve().parents[6]
    path = root/'ComputeNode/state/bell-retarded-kernels/source-reissue-rha0025-d8097db5cc/fresh-reference-ready.json'
    if not path.is_file():
        raise unittest.SkipTest('reissued original positive Ready source is required')
    ready = json.loads(path.read_text())
    parent = reference.ReferenceLocalPhaseSource(
        reference.reference.ReferenceAtomicClockSource.from_record(ready['source_record']), ready, raw_plan(Q(1, 10**8)))
    pulse = code.gaussian.GaussianAtomicPulseSource(parent, 0, sigma_squared_seconds=Q(25, 10**18),
        centre_seconds=Q(1, 10**8), duration_seconds=Q(1, 5*10**7))
    source = code.GaussianLocalDensitySource(pulse)
    initial = {(code.dipole.ION, code.dipole.ION): code.dipole.ComplexRadical(1)}
    trial = source.generate_trial(initial, Q(1, 10**12), slices=1, order=0, mode_bits=96)
    checked = source.certify(trial, coefficient_bits=128, envelope_order=6)
    return source, checked


def observed_certify_calls(action):
    calls = []; target = code.GaussianLocalDensitySource.certify.__code__; previous = sys.getprofile()
    def observe(frame, event, value):
        if event == 'call' and frame.f_code is target: calls.append(1)
    sys.setprofile(observe)
    try: result = action()
    finally: sys.setprofile(previous)
    return result, len(calls)


class DensityCheckedReuseControls(unittest.TestCase):
    def test_default_reuses_owned_complete_check(self):
        source, checked = fixture()
        result, calls = observed_certify_calls(lambda: source.verify(checked))
        self.assertEqual(result, checked); self.assertEqual(calls, 0)

    def test_explicit_override_rechecks_the_same_curve(self):
        source, checked = fixture()
        result, calls = observed_certify_calls(lambda: source.verify(checked, recheck=True))
        self.assertEqual(result, checked); self.assertEqual(calls, 1)
        with self.assertRaisesRegex(ValueError, 'Boolean'): source.verify(checked, recheck=1)

    def test_output_alias_and_wrong_price_do_not_poison_paid_result(self):
        source, checked = fixture(); value = source.verify(checked)
        value['whole_trace_norm_error'] = '0'
        self.assertEqual(source.verify(checked), checked)
        with self.assertRaisesRegex(ValueError, 'paid error changed'): source.verify(value)

    def test_same_shape_wrong_source_rejected_before_cache(self):
        source, checked = fixture(); bad = copy.deepcopy(checked)
        bad['source_record']['Gaussian_source']['phase_radians'] = '1/3'
        with self.assertRaisesRegex(ValueError, 'same original source'): source.verify(bad)


if __name__ == '__main__':
    unittest.main()
