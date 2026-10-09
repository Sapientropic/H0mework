from copy import deepcopy
from fractions import Fraction as Q
from itertools import product
from types import SimpleNamespace
import unittest

import shared_background_rha0030 as primary
import shared_background_independent_rha0030 as independent


def trials(alternating=False, count=2048):
    result = []
    for i in range(count):
        c = i % 8; event = (1 if (i//8) % 2 else 2) if alternating else 0
        result.append(SimpleNamespace(row=i+1, row_a=2*i, row_b=3*i, time_ms=Q(1000+i, 2),
            h=c//4, a=(c//2) % 2, b=c % 2, x=event//2, y=event % 2))
    return result


class SharedBackgroundControls(unittest.TestCase):
    def test_source_vertices_are_positive_supermeans(self):
        for a, b, t, occupied in product((Q(0), Q(1, 3), Q(1)), (Q(0), Q(2, 3), Q(1)), primary.TILTS, range(4)):
            r = [Q(int(i == occupied)) for i in range(4)]
            q = ((1-a)*(1-b)*r[0], (1-a)*(r[1]+b*r[0]),
                 (1-b)*(r[2]+a*r[0]), r[3]+a*r[1]+b*r[2]+a*b*r[0])
            self.assertEqual(sum(q), 1); self.assertGreaterEqual(min(q), 0)
            for face in primary.FACES:
                factors = [primary.factor(face, t, (1, 1), e, a, b) for e in range(4)]
                self.assertGreaterEqual(min(factors), 0)
                self.assertLessEqual(sum(p*f for p, f in zip(q, factors)), 1)

    def test_independent_rectangle_price_covers_interior(self):
        box = ((Q(1, 8), Q(3, 4)), (Q(1, 4), Q(7, 8)))
        for face, code, t in product(primary.FACES, product((0, 1), repeat=2), primary.TILTS):
            values = primary.minimum_factors(box, face, t, code)
            self.assertEqual(values, independent.minimum_factors(box, face, t, code))
            for e, a, b in product(range(4), (Q(1, 3), Q(1, 2)), (Q(2, 5), Q(3, 4))):
                self.assertLessEqual(values[e], primary.factor(face, t, code, e, a, b))

    def test_log_one_is_exact_zero(self):
        prices = primary.Prices()
        self.assertEqual(prices.log_lower(Q(1)), 0)
        self.assertEqual(independent.LogCheck().lower(Q(1)), 0)
        self.assertGreaterEqual(Q(prices.threshold, primary.GRID),
            Q(independent.LogCheck().threshold.hi, independent.LogCheck().arithmetic.scale))

    def test_high_background_excluded_zero_background_retained(self):
        history = primary.histories(trials()); prices = primary.Prices()
        self.assertIsNotNone(primary.witness(history, ((Q(3, 4), Q(1)), (Q(3, 4), Q(1))), (1, 1), prices))
        self.assertIsNone(primary.witness(history, ((Q(0), Q(0)), (Q(0), Q(0))), (1, 1), prices))

    def test_joint_face_excludes_balanced_anticorrelation(self):
        data = trials(True); history = primary.histories(data); prices = primary.Prices()
        box = ((Q(9, 20), Q(11, 20)), (Q(9, 20), Q(11, 20)))
        proof = primary.witness(history, box, (1, 1), prices)
        self.assertIsNotNone(proof); self.assertEqual(proof['face'], 'joint')
        own_history, _, sha = independent.prefixes(data)
        self.assertEqual(sha, primary.record_sha(data))
        independent.check_witness(proof, box, [1, 1], own_history, independent.LogCheck(), prices.threshold)

    def test_simultaneous_raw_and_encoder_flip(self):
        for face, e, code in product(primary.FACES, range(4), product((0, 1), repeat=2)):
            self.assertEqual(primary.factor(face, Q(1, 2), code, e, Q(1, 3), Q(2, 5)),
                primary.factor(face, Q(1, 2), (1-code[0], code[1]), e ^ 2, Q(1, 3), Q(2, 5)))

    def test_count_clock_and_log_corruption_rejected(self):
        data = trials(True); prices = primary.Prices(); box = ((Q(9, 20), Q(11, 20)),)*2
        proof = primary.witness(primary.histories(data), box, (1, 1), prices)
        history, _, _ = independent.prefixes(data)
        for kind in ('count', 'clock', 'log'):
            bad = deepcopy(proof)
            if kind == 'count': bad['counts'][0] += 1
            elif kind == 'clock': bad['source_address']['unix_milliseconds'] = '0'
            else: bad['log_factor_lower_scaled'][0] = str(int(bad['log_factor_lower_scaled'][0])+primary.GRID)
            with self.assertRaises(ValueError):
                independent.check_witness(bad, box, [1, 1], history, independent.LogCheck(), prices.threshold)

    def test_finite_budget_override_and_missing_cover(self):
        data = trials(); prices = primary.Prices(); history = primary.histories(data)
        own, _, _ = independent.prefixes(data); logs = independent.LogCheck()
        domain = primary.tree(history, (1, 1), prices, maximum_depth=0)
        result, _ = independent.check_tree(domain, own, logs, prices.threshold)
        self.assertEqual(result['unresolved_background_area'], '1')
        domain = primary.tree(history, (1, 1), prices, maximum_depth=2)
        independent.check_tree(domain, own, logs, prices.threshold)
        domain['nodes'].pop()
        with self.assertRaises(ValueError): independent.check_tree(domain, own, logs, prices.threshold)


if __name__ == '__main__':
    unittest.main()
