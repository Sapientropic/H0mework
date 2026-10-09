"""Same reference controls generate Gaussian full33 operator amplitudes."""
import copy
from fractions import Fraction as Q
from functools import lru_cache
import json
from pathlib import Path
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import gaussian_atomic_pulse_source as code
from test_reference_response_window_source import parent_fixture
from test_fourier_reference_local_programme_source import raw_plan


NS=Q(1,10**9)


@lru_cache(maxsize=1)
def parent():
    return code.reference.ReferenceLocalPhaseSource.with_clock_plans(parent_fixture(),raw_plan(Q(1,10**6)))


@lru_cache(maxsize=1)
def source():
    return code.GaussianAtomicPulseSource(parent(),0,sigma_squared_seconds=(5*NS)**2,
        centre_seconds=10*NS,duration_seconds=20*NS)


class GaussianPulseControls(unittest.TestCase):
    def test_original_reference_H_R_and_all33_loss_identity_with_nonstationary_ground(self):
        pulse=source();raw=pulse.record();parent_raw=parent().record()
        self.assertEqual(raw['working_atomic_owner'],parent_raw['working_atomic_owner'])
        self.assertEqual(raw['working_common_optical_source'],parent_raw['working_common_optical_source'])
        self.assertEqual(raw['working_aperture_source'],parent_raw['working_aperture_source'])
        self.assertEqual(raw['original_constant_excitation_controls'],parent_raw['source_generated_local_plans'][0][-1])
        self.assertTrue(raw['duration_is_certification_horizon'])
        self.assertFalse(raw['Gaussian_zero_at_endpoint_assumed'])
        self.assertFalse(raw['raw_peak_is_actual_pi_pulse_certification'])
        self.assertTrue(any(i!=j for i,j,v in raw['complete_static_H_per_second']))
        for time in (0,10*NS,20*NS):
            generator=pulse.generator(time)
            h,k,r=map(code._matrix,(generator['complete_H'],generator['complete_K'],generator['complete_R']))
            self.assertEqual(h,code.dipole.matrix_adjoint(h))
            self.assertFalse(code._sum(k,code.dipole.matrix_adjoint(k),r))
            self.assertTrue(any(code.dipole.STATES[i].family=='D2' and code.dipole.STATES[j].family=='ground' for i,j in k))
            self.assertEqual(code._matrix(generator['complete_R']),code._matrix(raw['complete_natural_R_per_second']))
        jet=pulse.hamiltonian_jet(10*NS,2)
        self.assertEqual([d['order'] for d in jet['jets']],[0,1,2])
        self.assertTrue(all(code._matrix(d['complete_H_derivative'])==code.dipole.matrix_adjoint(code._matrix(d['complete_H_derivative']))
                            for d in jet['jets']))
        self.assertTrue(all(d['complete_H_derivative'] for d in jet['jets']))

    def test_width_phase_side_override_and_real_Gaussian_tail_payment(self):
        pulse=source();raw=pulse.record()
        changed=code.GaussianAtomicPulseSource(parent(),1,sigma_squared_seconds=(8*NS)**2,
            centre_seconds=10*NS,duration_seconds=30*NS,phase_radians=Q(1,3))
        self.assertNotEqual(changed.generator(10*NS)['complete_H'],pulse.generator(10*NS)['complete_H'])
        self.assertEqual(changed.record()['reference_local_parent'],raw['reference_local_parent'])
        self.assertNotEqual(changed.record()['duration_seconds'],raw['duration_seconds'])
        at_end=pulse.field_off_tail_price(20*NS);late=pulse.field_off_tail_price(80*NS)
        self.assertGreater(Q(at_end['no_jump_operator_Duhamel_price_upper']),0)
        self.assertLess(Q(late['no_jump_operator_Duhamel_price_upper']),Q(at_end['no_jump_operator_Duhamel_price_upper']))
        self.assertEqual(Q(at_end['density_CP_Duhamel_price_per_input_norm_upper']),
                         2*Q(at_end['no_jump_operator_Duhamel_price_upper']))
        self.assertGreater(pulse.Gamma_math_price(3*NS,20*NS),0)
        self.assertEqual(pulse.Gamma_math_price(8*NS,8*NS),0)

    def test_operator_U_t_s_uses_I_at_s_and_full_nonHermitian_amplitude_residual(self):
        pulse=source()
        saved=json.loads(Path('/tmp/Gaussian-atomic-pulse-untrusted-focused-record.json').read_text())
        raw=pulse.record()
        self.assertEqual({k:v for k,v in saved['source_record'].items() if k!='source_bindings'},
                         {k:v for k,v in raw.items() if k!='source_bindings'})
        trial=copy.deepcopy(saved['untrusted_trial']);trial['source_record']=raw
        report=pulse.certify_operator(trial,coefficient_bits=160,phase_bits=160,envelope_order=6)
        with Path('/tmp/Gaussian-atomic-pulse-rounding-focused-record.json').open('x') as handle:
            json.dump({'source_record':pulse.record(),'certificate':report},handle,sort_keys=True)
        self.assertEqual(report['source_interval_seconds'],list(map(str,(3*NS,20*NS))))
        self.assertEqual(report['initial_operator'],'I at s')
        self.assertFalse(report['inverse_U_t0_used'])
        self.assertFalse(report['operator_amplitude_Hermitian_projected'])
        self.assertEqual(Q(report['outward_price_rounding']['increment_upper_per_scalar_ceil']),Q(1,1<<160))
        self.assertFalse(report['outward_price_rounding']['integer_output_limit_disabled'])
        h,price=pulse.hamiltonian(10*NS,bits=160)
        self.assertEqual(h,code.dipole.matrix_adjoint(h))
        self.assertGreaterEqual(price,0)
        operator=code._matrix(report['full33_operator'])
        self.assertNotEqual(operator,code.dipole.matrix_adjoint(operator))
        self.assertGreater(len(operator),33)
        self.assertLess(Q(report['operator_norm_error_upper']),Q(1,2))
        self.assertGreater(Q(report['Gamma_math_operator_price']),0)
        local=sum((Q(p[name]) for p in report['complete_piece_prices'] for name in
            ('join_operator_error','true_K_polynomial_residual_price','source_coefficient_and_Gaussian_tail_price','endpoint_mode_evaluation_price')),Q(0))
        self.assertEqual(Q(report['rotating_operator_error']),local)
        self.assertEqual(Q(report['operator_norm_error_upper']),local+Q(report['frame_endpoint_scalar_price'])+Q(report['Gamma_math_operator_price']))
        self.assertTrue(pulse.verify_operator(report))
        empty=pulse.generate_operator_trials(8*NS,8*NS,mode_bits=128)
        exact=pulse.certify_operator(empty)
        self.assertEqual(code._matrix(exact['full33_operator']),{(i,i):code.dipole.ComplexRadical(1) for i in range(33)})
        self.assertEqual(Q(exact['operator_norm_error_upper']),0)
        # A different carrier phase at s cannot be reconstructed using only D(t).
        # Use a D2 input column to exercise the independent right-end phase.
        d2=next(i for i,s in enumerate(code.dipole.STATES) if s.family=='D2')
        a,_=code._restore(pulse.record(),{(0,d2):(Q(1),Q(0))},3*NS,20*NS,160)
        b,_=code._restore(pulse.record(),{(0,d2):(Q(1),Q(0))},0,20*NS,160)
        self.assertNotEqual(a,b)
        wrong=copy.deepcopy(empty);wrong['source_record']['sigma_squared_seconds']=str((6*NS)**2)
        with self.assertRaisesRegex(ValueError,'same original Gaussian'):
            pulse.certify_operator(wrong)

    def test_target_generator_lookalike_and_source_or_actual_helper_mutation_rejected(self):
        pulse=source();raw=pulse.record()
        with self.assertRaisesRegex(ValueError,'closed same reference'):
            code.GaussianAtomicPulseSource(SimpleNamespace(record=lambda:raw['reference_local_parent']),0,
                sigma_squared_seconds=NS**2,centre_seconds=NS,duration_seconds=2*NS)
        with patch.object(code,'_envelope_polynomial',lambda *a:([1],0)),self.assertRaisesRegex(ValueError,'closure changed'):
            pulse.record()
        bad=code.GaussianAtomicPulseSource(parent(),0,sigma_squared_seconds=NS**2,centre_seconds=NS,duration_seconds=2*NS)
        bad._frame['source_raising_operator_per_second']=[]
        with self.assertRaisesRegex(ValueError,'raw controls'):
            bad.record()
        with self.assertRaisesRegex(ValueError,'positive Gaussian'):
            code.GaussianAtomicPulseSource(parent(),0,sigma_squared_seconds=0,centre_seconds=NS,duration_seconds=2*NS)
        zero=pulse.generate_operator_trials(2*NS,2*NS)
        report=pulse.certify_operator(zero);wrong=copy.deepcopy(report);wrong['operator_norm_error_upper']='1'
        with self.assertRaisesRegex(ValueError,'price changed'):
            pulse.verify_operator(wrong)


class HigherGaussianOperatorControls(unittest.TestCase):
    def test_integer_residual_keeps_the_full_complex_reference_endpoint_and_price(self):
        pulse=source();raw=pulse.record();parts=code._parts(raw,160)
        block=code._source_blocks(raw)
        self.assertEqual(sorted(i for b in block for i in b),list(range(33)))
        # A small non-Hermitian witness exercises complex polynomial convolution.
        q=1<<128;trial={'duration_seconds':str(NS/16),'modes':[{
            'lambda_per_second':['0','0'],'coefficients':[[[0,0,q,0],[0,1,q//3,q//7]],[[1,0,q//11,-q//13]]]}]}
        initial={(i,i):(Q(1),Q(0)) for i in range(33)}
        old=code._piece(raw,trial,initial,3*NS,128,160,6,parts)
        new=code._piece_integer(raw,trial,initial,3*NS,128,160,6,parts)
        self.assertEqual(old[0:2],new[0:2])
        self.assertGreater(new[2],0)
        self.assertLessEqual(new[2],old[2]+Q(1,1<<110))
        norm=code._integer_norm({(0,0):{1:(3,4)},(0,1):{1:(5,0)}},1,160)
        # ||M||_2 <= sqrt(||M||_1 ||M||_infinity) <= their maximum.
        self.assertGreaterEqual(norm*norm,84)
        self.assertLessEqual(norm,12)
        self.assertTrue(new[3]['all_K_polynomial_rounding_paid'])
        self.assertFalse(new[3]['operator_amplitude_Hermitian_projected'])

    def test_source_high_order_operator_curve_reaches_the_driven_field_precision_gate(self):
        pulse=source()
        trial=pulse.generate_operator_trials(3*NS,20*NS,slices=64,order=48,mode_bits=160,coefficient_bits=192)
        with Path('/tmp/Gaussian-high-order-untrusted-focused-record.json').open('x') as handle:
            json.dump({'source_record':pulse.record(),'untrusted_trial':trial},handle,sort_keys=True)
        print('Gaussian-high-order-untrusted-saved',len(trial['pieces']),flush=True)
        report=pulse.certify_operator(trial,coefficient_bits=192,phase_bits=192,envelope_order=8)
        with Path('/tmp/Gaussian-high-order-operator-focused-record.json').open('x') as handle:
            json.dump({'source_record':pulse.record(),'certificate':report},handle,sort_keys=True)
        print('Gaussian-high-order-certified-error',float(Q(report['operator_norm_error_upper'])),flush=True)
        self.assertLess(Q(report['operator_norm_error_upper']),Q(1,10**8))
        self.assertEqual(report['initial_operator'],'I at s')
        self.assertGreater(len(report['full33_operator']),33)
        self.assertTrue(pulse.verify_operator(report))
        self.assertTrue(all(m['polynomial_degree']==48 for p in report['complete_piece_prices'] for m in p['complete_mode_prices']))


if __name__=='__main__':
    unittest.main()
