from copy import deepcopy
from fractions import Fraction as Q
from pathlib import Path
import cmath
import gzip
import json
import tempfile
import unittest

import chebyshev_density_rha0032 as core
import chebyshev_density_integer_rha0032_1 as integer
import chebyshev_density_proposal_rha0032 as old
import chebyshev_density_proposal_rha0032_2 as proposal
from test_chebyshev_density_rha0032 import raw, NS


def handoff(start, *, driven=False):
    source, e = raw(True); d = core.density.dipole
    source['complete_static_H_per_second'] = core.density.channel._input_record({(e, e): d.ComplexRadical(43/NS)})
    if driven:
        source['source_raising_operator_per_second'] = core.density.channel._input_record({(e, 0): d.ComplexRadical(250000000)})
        source['phase_radians'] = '1/7'
    initial = {(0, 0): d.ComplexRadical(Q(1, 2)), (e, e): d.ComplexRadical(Q(1, 2)),
        (0, e): d.ComplexRadical(Q(1, 2)), (e, 0): d.ComplexRadical(Q(1, 2))}
    return {'schema': 'stage10-source-issued-free-density-handoff/rha0032',
        'source_record': {'Gaussian_source': source}, 'complete_initial_matrix': core.density.channel._input_record(initial),
        'source_interval_seconds': [str(start), str(start+NS)], 'source_factor_id': 'synthetic-relative-clock'}, e


def curve(writer, hand, directory, name):
    path = Path(directory)/name; writer.propose(hand, path)
    with gzip.open(path, 'rt') as handle:
        header, piece = json.loads(next(handle)), json.loads(next(handle))
        if handle.read(): raise AssertionError('synthetic control must have exactly one full piece')
    source = hand['source_record']['Gaussian_source']
    initial = core.density.channel._read_input(hand['complete_initial_matrix'], 33)
    start = Q(hand['source_interval_seconds'][0])
    _, pairs, _ = core.density._rotating_initial(source, initial, start, 96)
    checked = integer.piece(core.density._Columns(source, 192), source, piece, pairs, start, 96, 20)
    return header, piece, checked


class RelativeClockControls(unittest.TestCase):
    def test_high_frequency_quiet_source_is_exactly_time_translation_invariant(self):
        early, e = handoff(NS); late, _ = handoff(101*NS)
        with tempfile.TemporaryDirectory() as directory:
            first = curve(proposal, early, directory, 'early.gz')
            last = curve(proposal, late, directory, 'late.gz')
            self.assertEqual(first[1], last[1])
            self.assertEqual(first[2][:2], last[2][:2])
            self.assertLess(first[2][2], Q(1, 10**8))
            self.assertLess(abs(complex(*map(float, first[2][1][0, e]))-.5*cmath.exp(43j)), 1e-12)
            self.assertFalse(first[0]['writer_correctness_assumed'])
            self.assertGreaterEqual(first[0]['numeric_mantissa_bits'], 53)

    def test_original_float_clock_remains_a_supported_untrusted_control(self):
        hand, _ = handoff(101*NS)
        with tempfile.TemporaryDirectory() as directory:
            previous = curve(old, hand, directory, 'old.gz')
            improved = curve(proposal, hand, directory, 'new.gz')
            self.assertEqual(previous[0]['source_record_sha256'], improved[0]['source_record_sha256'])
            self.assertEqual(previous[0]['initial_matrix_sha256'], improved[0]['initial_matrix_sha256'])
            self.assertLess(improved[2][2], previous[2][2])

    def test_nonzero_drive_and_changed_curve_still_pay_the_original_residual(self):
        hand, _ = handoff(NS, driven=True)
        with tempfile.TemporaryDirectory() as directory:
            _, piece, checked = curve(proposal, hand, directory, 'driven.gz')
            self.assertLess(checked[2], Q(1, 10**8))
            changed = deepcopy(piece); changed['chebyshev_coefficients'][1][0][2] += 1 << 80
            source = hand['source_record']['Gaussian_source']
            initial = core.density.channel._read_input(hand['complete_initial_matrix'], 33)
            _, pairs, _ = core.density._rotating_initial(source, initial, NS, 96)
            columns = core.density._Columns(source, 192)
            self.assertGreater(integer.piece(columns, source, changed, pairs, NS, 96, 20)[2], checked[2])


if __name__ == '__main__': unittest.main()
