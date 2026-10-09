from fractions import Fraction as Q
import copy
import unittest
import numpy as np
import positive_quadrature_rha0038 as quadrature
import dyadic_matrix_rha0038 as matrix


class LateRegisteredArithmeticControls(unittest.TestCase):
    def test_positive_complete_moment_default_and_explicit_smaller_rule(self):
        self.assertEqual(quadrature.propose.__defaults__,(160,296,192))
        grid=quadrature.propose(8,14); report=quadrature.check(grid)
        self.assertTrue(report['registered_accuracy_passed'])
        self.assertEqual(report['independent_monomial_integrals_checked'],15)
        self.assertEqual(report['independent_node_moments_checked'],[0,7,14])
        self.assertEqual(report['positive_node_count'],8)

    def test_lookalike_rule_and_bad_weights_fail(self):
        grid=quadrature.propose(8,16)
        self.assertFalse(quadrature.check(grid)['registered_accuracy_passed'])
        bad=copy.deepcopy(grid); bad['nodes_and_weights'][0][1]=-1
        with self.assertRaises(ValueError):quadrature.check(bad)
        bad=copy.deepcopy(grid);bad['nodes_and_weights'][1]=bad['nodes_and_weights'][0]
        with self.assertRaises(ValueError):quadrature.check(bad)

    def test_exact_96bit_signed_products_match_independent_integer_dot(self):
        generator=np.random.default_rng(381)
        a=np.array([[int(x)*(1 << 70)+int(y) for x,y in zip(row,tail)]
            for row,tail in zip(generator.integers(-100,100,(9,73)),generator.integers(-100,100,(9,73)))],dtype=object)
        b=np.array([[int(x)*(1 << 35)+int(y) for x,y in zip(row,tail)]
            for row,tail in zip(generator.integers(-100,100,(73,7)),generator.integers(-100,100,(73,7)))],dtype=object)
        self.assertTrue(np.array_equal(matrix.integer_product(a,b),a@b))
        r,i=matrix.complex_product((a,-a),(b,b))
        self.assertTrue(np.array_equal(r,2*(a@b)));self.assertTrue(np.array_equal(i,np.zeros((9,7),dtype=object)))

    def test_float_coefficients_and_overflow_shapes_rejected(self):
        with self.assertRaises(ValueError):matrix.integer_product([[1.0]],[[1]])
        with self.assertRaises(ValueError):matrix.integer_product(np.zeros((1,32769),dtype=object),np.zeros((32769,1),dtype=object))

    def test_sparse_complex_products_and_exact_rounding_price(self):
        left={(0,0):(5,3),(1,0):(-2,1)};right={(0,1):(7,-2)}
        out,price=matrix.multiply(left,right,bits=4)
        self.assertEqual(out,{(0,1):(3,1),(1,1):(-1,1)})
        exact={(0,1):(41,11),(1,1):(-12,11)}
        expected=sum(Q(abs(a-out[key][0]*16)+abs(b-out[key][1]*16),256) for key,(a,b) in exact.items())
        self.assertEqual(price,expected)
        self.assertEqual(matrix.adjoint(matrix.adjoint(out)),out)


if __name__ == '__main__':unittest.main()
