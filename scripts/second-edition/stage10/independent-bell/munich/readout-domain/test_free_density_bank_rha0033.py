from copy import deepcopy
from fractions import Fraction as Q
import unittest

import free_density_bank_rha0033 as code


def inventory():
    banks = [[{'factor_id': 'a0'}, {'factor_id': 'a1'}], [{'factor_id': 'b0'}, {'factor_id': 'b1'}]]
    terms = [['a0', 'b1'], ['a1', 'b0']]
    return {'checked_local_density_inventories': banks, 'source_factor_ids': terms,
        'source_issued_two_pump_source': {'source_issued_two_pump_factor_inlets': deepcopy(banks),
                                         'source_tensor_factor_ids': deepcopy(terms)}}


class CompleteFreeBankControls(unittest.TestCase):
    def test_complete_inventory_default_and_explicit_other_side_override(self):
        raw = inventory()
        self.assertEqual(code.choose(raw), (0, 0, 'a0'))
        self.assertEqual(code.choose(raw, 1, 1), (1, 1, 'b1'))
        self.assertEqual(len(code.inventory(raw)), 4)

    def test_lookalike_bank_with_changed_incidence_or_factor_order_is_rejected(self):
        raw = inventory(); raw['source_factor_ids'][0][0] = 'b0'
        with self.assertRaises(ValueError): code.inventory(raw)
        raw = inventory(); raw['checked_local_density_inventories'][0].reverse()
        with self.assertRaises(ValueError): code.inventory(raw)
        for side, index in ((-1, 0), (0, -1), (0, 2), (True, 0)):
            with self.assertRaises(ValueError): code.choose(inventory(), side, index)

    def test_signed_tensor_error_uses_all_incidence_and_pays_cross_term(self):
        reports = {(0, 'a'): {'initial_entry_norm_upper': '3/2', 'whole_new_trace_norm_error': '1/7'},
                   (1, 'b'): {'initial_entry_norm_upper': '2/3', 'whole_new_trace_norm_error': '1/11'}}
        total, rows = code.tensor_price([['a', 'b'], ['a', 'b']], reports)
        one = Q(1, 7)*Q(2, 3)+Q(1, 11)*Q(3, 2)+Q(1, 77)
        self.assertEqual(total, 2*one); self.assertEqual(len(rows), 2)
        # For negative real source factors the full outward perturbation can attain this price.
        self.assertEqual(abs((-Q(3, 2)-Q(1, 7))*(-Q(2, 3)-Q(1, 11))-Q(1)), one)


if __name__ == '__main__': unittest.main()
