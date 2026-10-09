from fractions import Fraction as Q
from functools import lru_cache
from types import SimpleNamespace
import unittest

import zero_count_quantum_source_rha0042 as code
from test_retarded_gaussian_trajectory_source import fixture, NS
from test_registered_tensor_action_rha0034 import inputs


@lru_cache(maxsize=1)
def parents():
    original = fixture()
    priority = code.flux.FirstReceiptFluxSource(original._law)
    return original, priority


def expand(terms):
    result = {}
    for coefficient, a, b in terms:
        code.base.law._add(result, code.tensor.factors._tensor(a, b), coefficient)
    return result


class CompleteQuantumRestrictionControls(unittest.TestCase):
    def test_all_priority_queries_close_original_full_quantum_components(self):
        original, priority = parents()
        a, b = inputs()
        matrix = code.tensor.factors._tensor(a, b)
        state = {}
        for index, mark in enumerate(original._marks):
            if mark.receipt is None:
                for (i, j), z in matrix.items():
                    state[mark, i, j] = z*Q(index+1, 11)
        for item in priority.record()['complete_no_count_queries']:
            query = code.NoCountQuantumSource(original, priority, item['query'])
            for component in code.trajectory.COMPONENTS:
                self.assertEqual(query.component_action(component, query.project(state), slice_start=3*NS),
                    query.project(original.component_action(component, state, slice_start=3*NS)))
            self.assertFalse(query.record()['local_factorization_assumed'])

    def test_source_default_override_tensor_action_and_unequal_clock_components(self):
        original, priority = parents()
        query = code.NoCountQuantumSource(original, priority)
        self.assertTrue(query.record()['query']['requires_coupled_no_count_flow'])
        a, b = inputs()
        terms = ((code.dipole.ComplexRadical(Q(2, 7), Q(1, 5)), a, b),)
        for name in (query.record()['query']['query'], 'all', 'perp'):
            selected = code.NoCountQuantumSource(original, priority, name)
            for component in code.trajectory.COMPONENTS:
                self.assertEqual(expand(selected.tensor_component_action(component, terms, slice_start=3*NS)),
                    selected.component_action(component, expand(terms), slice_start=3*NS))
        scalars = query.slice_components(3*NS, 4*NS)
        self.assertEqual([r['component'] for r in scalars['components']],
                         ['quiet', ['drive', 0], ['drive', 1], ['cross', 0, 1], ['cross', 1, 0]])
        self.assertTrue(scalars['same_original_scalar_components'])
        self.assertFalse(query.record()['CEM_time_mother_issued'])

    def test_lookalike_source_wrong_query_birth_cut_and_initial_owner_are_rejected(self):
        original, priority = parents()
        with self.assertRaisesRegex(ValueError, 'same closed'):
            code.NoCountQuantumSource(SimpleNamespace(record=original.record), priority)
        with self.assertRaisesRegex(ValueError, 'priority-issued'):
            code.NoCountQuantumSource(original, priority, 'no-0')
        query = code.NoCountQuantumSource(original, priority)
        with self.assertRaisesRegex(ValueError, 'fixed original detector gate'):
            query.component_action('quiet', {}, slice_start=121*NS)
        with self.assertRaisesRegex(ValueError, 'activation boundary'):
            query.slice_components(NS/2, 3*NS/2)
        with self.assertRaisesRegex(ValueError, 'source-issued complete'):
            code.NoCountPrimalInlet(SimpleNamespace(record=lambda: {}), query)
        original._law.record()

    def test_physical_quantum_action_is_the_same_original_Mark_restriction(self):
        original, priority = parents()
        query = code.NoCountQuantumSource(original, priority)
        a, b = inputs()
        matrix = code.tensor.factors._tensor(a, b)
        state = {(mark, i, j): z*Q(index+1, 11)
            for index, mark in enumerate(original._marks) if mark.receipt is None
            for (i, j), z in matrix.items()}
        actual, _ = original._law.marked_action(3*NS, state, bits=192)
        value, error = query.physical_action(3*NS, query.project(state))
        self.assertEqual(value, query.project(actual))
        self.assertGreaterEqual(error, 0)
