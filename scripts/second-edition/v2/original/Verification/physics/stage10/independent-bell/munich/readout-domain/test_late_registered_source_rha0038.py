import copy
from fractions import Fraction as Q
from types import SimpleNamespace
import unittest
import late_registered_source_rha0038 as source
import late_registered_independent_rha0038 as independent
from test_retarded_gaussian_bsm_source import fixture


class LateRegisteredSourceControls(unittest.TestCase):
    def test_original_full_bath_and_coherent_four_port_effects(self):
        raw,blocks,rows,same=source.compile_jumps(fixture())
        self.assertEqual(independent.raw_jumps(raw),(blocks,rows,same))
        self.assertEqual(len(rows),40);self.assertEqual([r['physical_natural_jumps'] for r in blocks],[30,30])
        self.assertEqual({r['port'] for r in rows},{0,1,2,3})
        self.assertEqual(len({tuple(r['group']) for r in rows}),10)
        self.assertTrue(all(r['ground_compression_zero_complex_units_covered_per_jump']==1025 for r in blocks))
        for row in rows:
            self.assertEqual(len(row['local_operators']),2)
            for encoded in row['local_operators']:
                matrix=source.gaussian._matrix(encoded)
                self.assertTrue(all(source.dipole.STATES[i].family=='ground' and
                    source.dipole.STATES[j].family==row['group'][0] for i,j in matrix))
        self.assertTrue(all(m for side in same for m in side))

    def test_closed_owner_and_source_block_negative_controls(self):
        original=fixture()
        with self.assertRaises(ValueError):source.compile_jumps(SimpleNamespace(record=original.record))
        raw=original.record();bad=copy.deepcopy(raw)
        h=bad['complete_driven_field_source']['Gaussian_source_legs'][0]['complete_static_H_per_second']
        g=next(i for i,s in enumerate(source.dipole.STATES) if s.family=='ground')
        e=next(i for i,s in enumerate(source.dipole.STATES) if s.family=='D2')
        h.extend(source.channel._input_record({(g,e):source.dipole.ComplexRadical(1),(e,g):source.dipole.ComplexRadical(1)}))
        with self.assertRaises(ValueError):source.static_blocks(bad)


if __name__=='__main__':unittest.main()
