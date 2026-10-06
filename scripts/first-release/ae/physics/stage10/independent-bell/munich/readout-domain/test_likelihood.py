import hashlib
import math
import unittest
from decimal import Decimal, localcontext
from fractions import Fraction as Q
from itertools import product

from model import Effect, Instrument, full_joint
from likelihood import Directed, Interval, PrefixChecker, fraction_bytes


def beta_likelihood(counts):
    return Q(math.prod(math.prod(range(1, 2 * n, 2)) for n in counts),
             (2 ** sum(counts)) * math.factorial(sum(counts)))


def dirichlet_likelihood(counts):
    return Q(math.prod(math.prod(range(1, 2 * n, 2)) for n in counts),
             (2 ** sum(counts)) * math.factorial(sum(counts) + 1))


def closed_components(checker):
    conditional_num = math.prod(beta_likelihood(counts) for counts in checker.complement.values())
    full_num = math.prod(dirichlet_likelihood(counts) for counts in checker.counts.values())
    denominators = [Q(1)] * 4
    for context, counts in checker.counts.items():
        q = checker.table[context]
        for i, number in enumerate(counts):
            x, y = divmod(i, 2)
            mass = q[0] + q[3] if x == y else q[1] + q[2]
            denominators[0] *= (q[i] / mass) ** number
            denominators[1] *= (q[2*x] + q[2*x+1]) ** number
            denominators[2] *= (q[y] + q[2+y]) ** number
            denominators[3] *= q[i] ** number
    return tuple(n / d for n, d in zip((conditional_num, beta_likelihood(checker.alice),
                                        beta_likelihood(checker.bob), full_num), denominators))


class StatisticsTests(unittest.TestCase):
    def table(self):
        source = Instrument((Effect('1/10', '1/3', '1/4'), Effect('-1/5', '-1/5', '1/3')),
                            (Effect('1/8', '1/3', '-1/4'), Effect('-1/7', '1/4', '1/3')))
        return {(r['h'], r['a'], r['b']): r['probabilities'] for r in full_joint(source)}

    def test_every_small_prefix_encloses_independent_closed_form(self):
        checker = PrefixChecker(self.table())
        sequence = list(product(range(2), repeat=5))
        for row in sequence:
            log_e = checker.step(*row)
            components = closed_components(checker)
            actual = (components[0] + components[1] + components[2]) / 6 + components[3] / 2
            exp = checker.directed.exponential(log_e)
            self.assertLessEqual(Q(exp.lower), actual)
            self.assertGreaterEqual(Q(exp.upper), actual)
        self.assertEqual(checker.result()['trials'], 32)

    def test_decimal_default_context_cannot_round_interval_negation(self):
        math_context = Directed(80)
        value = Interval(Decimal('1.12345678901234567890123456789012345678901234567890'),
                         Decimal('1.12345678901234567890123456789012345678901234567891'))
        with localcontext() as context:
            context.prec = 6
            result = math_context.subtract(Interval(Decimal(0), Decimal(0)), value)
        self.assertEqual(result.lower, value.upper.copy_negate())
        self.assertEqual(result.upper, value.lower.copy_negate())

    def test_exact_factor_encoding_and_positive_domain(self):
        raw = b'\0' * 7 + b'\1\3' + b'\0' * 7 + b'\1\2'
        self.assertEqual(fraction_bytes(Q(3, 2)), raw)
        self.assertEqual(hashlib.sha256(fraction_bytes(Q(6, 4))).digest(), hashlib.sha256(raw).digest())
        for bad in (Q(0), Q(-1)):
            with self.assertRaises(ValueError):
                fraction_bytes(bad)

    def test_model_zero_event_is_not_epsilon_smoothed(self):
        table = {key: (Q(1), Q(0), Q(0), Q(0)) for key in product(range(2), repeat=3)}
        checker = PrefixChecker(table)
        with self.assertRaisesRegex(ValueError, 'zero-probability'):
            checker.step(0, 0, 0, 0, 1)

    def test_source_like_wrong_model_excluded_and_all_prefixes_retained(self):
        table = {key: (Q(1, 4),) * 4 for key in product(range(2), repeat=3)}
        checker = PrefixChecker(table)
        for _ in range(40):
            checker.step(0, 0, 0, 0, 0)
        result = checker.result()
        self.assertEqual(result['status'], 'point_excluded')
        self.assertLess(result['first_rejection'], result['trials'])
        self.assertEqual(result['trials'], 40)

    def test_own_setting_model_marginal_is_consumed(self):
        checker = PrefixChecker(self.table())
        checker.step(0, 0, 0, 0, 0)
        checker.step(1, 1, 1, 1, 1)
        components = closed_components(checker)
        for component, log_range in zip(components, checker.logs):
            exp_range = checker.directed.exponential(log_range)
            self.assertLessEqual(Q(exp_range.lower), component)
            self.assertGreaterEqual(Q(exp_range.upper), component)

    def test_forecasters_initial_one_and_no_empty_pass(self):
        table = {key: (Q(1, 4),) * 4 for key in product(range(2), repeat=3)}
        checker = PrefixChecker(table)
        self.assertEqual(checker.result()['status'], 'inconclusive')
        value = checker.step(0, 0, 0, 0, 0)
        self.assertLessEqual(value.lower, 0)
        self.assertGreaterEqual(value.upper, 0)
        self.assertEqual(checker.result()['status'], 'all_prefix_witness_verified')


if __name__ == '__main__':
    unittest.main()
