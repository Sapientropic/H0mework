from fractions import Fraction as Q
from types import SimpleNamespace
import unittest

import registered_tensor_action_rha0034 as code
from test_retarded_gaussian_trajectory_source import fixture, NS


def inputs():
    d = code.dipole; g = d.INDEX[d.State('ground', 1, -1)]; e = d.INDEX[d.State('D2', 2, 0)]
    a = {(g, e): d.ComplexRadical(Q(2, 7), Q(1, 5)), (e, g): d.ComplexRadical(Q(2, 7), Q(-1, 5)),
         (e, e): d.ComplexRadical(Q(-3, 11))}
    b = {(g, e): d.ComplexRadical(Q(-1, 3), Q(2, 9)), (e, g): d.ComplexRadical(Q(-1, 3), Q(-2, 9)),
         (e, e): d.ComplexRadical(Q(5, 13))}
    return a, b


class RegisteredTensorControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.original = fixture(); cls.split = code.source.RetardedRegisteredDuhamelSource(cls.original)

    def test_all_marks_components_and_activations_match_original_actions(self):
        self.split.record(); a, b = inputs()
        for active in ((False, False), (False, True), (True, False), (True, True)):
            for mark in self.original._marks:
                state = code.expand(((mark, code.dipole.ComplexRadical(1), a, b),))
                blocks = self.original._blocks(state)
                for component in code.trajectory.COMPONENTS:
                    for part, old in (('free', code.source._free_component), ('registered', code.source._registered_component)):
                        actual = code._apply_rows(code._rows(self.original, part, component, mark, active), code.dipole.ComplexRadical(1), a, b)
                        self.assertEqual(code.expand(code.merge(actual)), old(self.original, component, blocks, active))
        self.split.record()

    def test_default_registered_and_explicit_complete_generator_override(self):
        a, b = inputs(); terms = ((code.bsm.INITIAL, code.dipole.ComplexRadical(1), a, b),); state = code.expand(terms)
        for component in code.trajectory.COMPONENTS:
            self.assertEqual(code.expand(code.apply(self.split, component, terms, slice_start=3*NS)),
                self.split.registered_component_action(component, state, slice_start=3*NS))
            self.assertEqual(code.expand(code.apply(self.split, component, terms, slice_start=3*NS, part='full')),
                self.original.component_action(component, state, slice_start=3*NS))

    def test_lookalike_source_bad_coordinate_and_unknown_part_are_rejected(self):
        with self.assertRaises(ValueError): code.apply(SimpleNamespace(record=self.split.record), 'quiet', (), slice_start=3*NS)
        a, b = inputs(); a[33, 0] = code.dipole.ComplexRadical(1)
        with self.assertRaises(ValueError): code.apply(self.split, 'quiet', ((code.bsm.INITIAL, 1, a, b),), slice_start=3*NS)
        with self.assertRaises(ValueError): code.apply(self.split, 'quiet', (), slice_start=3*NS, part='truncated')

    def test_source_layers_generate_the_exact_finite_truncation_residual(self):
        a, b = inputs(); initial = code.bsm.INITIAL
        one = code.bsm.BSMSource.target(self.original._law._gate, initial, 0)
        layers = (((initial, code.dipole.ComplexRadical(1), a, b),),
                  ((one, code.dipole.ComplexRadical(Q(1, 7)), a, b),),
                  ((initial, code.dipole.ComplexRadical(Q(-2, 9)), a, b),))
        complete = code.expand(tuple(term for layer in layers for term in layer)); _, active = self.original._clock(3*NS)
        for component in code.trajectory.COMPONENTS:
            result = code.layer_rhs(self.split, component, layers, slice_start=3*NS)
            actual = code.expand(tuple(term for layer in result for term in layer))
            expected = self.original._component(component, self.original._blocks(complete), active)
            omitted = code.source._registered_component(self.original, component, self.original._blocks(code.expand(layers[-1])), active)
            code.trajectory._add(expected, omitted, -1)
            self.assertEqual(actual, expected)
        with self.assertRaises(ValueError): code.layer_rhs(self.split, 'quiet', (), slice_start=3*NS)


if __name__ == '__main__': unittest.main()
