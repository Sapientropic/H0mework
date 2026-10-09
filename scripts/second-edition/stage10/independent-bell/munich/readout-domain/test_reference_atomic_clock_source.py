"""Strict reference pi and source-born physical CP/action controls."""
import copy
from fractions import Fraction as Q
from functools import lru_cache
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import reference_atomic_clock_source as code
from test_munich_atomic_programme import TRANSFERS,MOMENTS


@lru_cache(maxsize=1)
def source_fixture():
    occupations=tuple(dict.fromkeys(code.native.trap.GROUND,0) for _ in (0,1))
    couplings=tuple(dict.fromkeys(code.native.trap.GROUND,0) for _ in (0,1))
    ground=code.dipole.State('ground',2,2)
    for side in (0,1):
        occupations[side][ground]=1;couplings[side][ground]=Q(side+1,4)
    drives=(code.atomic.Drive('cooling','east',Q(1,2),Q(-1,2),'sigma+'),
            code.atomic.Drive('repump','west',0,0,'sigma-'))
    rules=(code.persistent.PollRule('loading',(True,True),(True,True),1,'loading','ready',
                (None,None),(True,True),False),
           code.persistent.PollRule('ready',(True,True),(False,False),1,'loading','ready',
                (False,False),(True,True),True))
    source,pack=code.ReferenceAtomicClockSource.from_paid_run('2016-04-15',beam_transfers=TRANSFERS,
        magnetic_fields=(Q(1,1000),Q(-1,2000)),magnetic_moments=MOMENTS,
        collection_a=((Q(1,10),0,0),(0,0,Q(1,10))),collection_b=((Q(1,10),0,0),(0,0,Q(1,10))),
        splitter=code.native.photons.balanced_beam_splitter() if hasattr(code.native,'photons') else code.optical.optics.balanced_beam_splitter(),
        efficiencies=(Q(1,2),)*4,background_rates=(Q(1,1000),Q(2,1000),Q(3,1000),Q(4,1000)),
        reservoir_occupations=occupations,capture_couplings=couplings,drives=(drives,drives),rules=rules,
        seed={'stage':'loading','loaded_flags':(False,False),'clock_seconds':0,'recent_arrivals_seconds':(),
              'atomic_primitives':(code.dipole.STATES[code.dipole.ION],)*2},
        physical_duration_seconds=Q(1,50000000),poll_period_seconds=Q(1,50000000))
    return source,pack


@lru_cache(maxsize=1)
def certified_fixture():
    source,pack=source_fixture();trial=source.generate_trial(order=40)
    report=source.certify(trial)
    Path('/tmp/reference-atomic-clock-focused-record.json').write_text(json.dumps({
        'source_record':source.record(),'source_package':pack,'untrusted_curve':trial,'certificate':report,
        'scope':'source-issued primitive and declared normalized raw hardware leaf in the frozen reference model; no actual calibration or public score'
    },sort_keys=True),encoding='utf-8')
    return source,report


class ReferenceClockArithmeticControls(unittest.TestCase):
    def test_machin_exact_tail_and_generated_reference_scale(self):
        coarse=code.reference_clock(terms=20,bits=96);fine=code.reference_clock()
        a,b=map(Q,coarse['pi_enclosure']);c,d=map(Q,fine['pi_enclosure'])
        self.assertLess(a,c);self.assertLess(d,b)
        self.assertLess(d-c,Q(1,10**55))
        glo,ghi=map(Q,fine['angular_Gamma_enclosure_per_second'])
        ulo,uhi=map(Q,fine['seconds_per_source_unit_enclosure'])
        self.assertEqual((glo,ghi),(2*5750000*c,2*5750000*d))
        self.assertEqual((ulo,uhi),(1/ghi,1/glo))
        self.assertTrue(code.verify_reference_clock(fine))
        changed=copy.deepcopy(fine);changed['Gamma_numerical_error']='0'
        with self.assertRaisesRegex(ValueError,'enclosure changed'):
            code.verify_reference_clock(changed)
        self.assertFalse(fine['pi_is_an_unknown_hardware_coordinate'])

    def test_exact_physical_pullback_is_a_rational_curve_readout_without_rounding(self):
        gamma=Q(code.reference_clock()['Gamma_numerical_centre']);bits=160
        pieces=[{'duration':'7/13','modes':[{'lambda':[11,-19],'coefficients':[[[0,1088,1088,3,0]]]}]}]
        physical=code._exact_physical_pullback(pieces,gamma,bits)
        self.assertEqual(Q(physical[0]['duration_seconds'])*gamma,Q(7,13))
        self.assertEqual([Q(value)/gamma for value in physical[0]['modes'][0]['lambda_per_second']],
                         [Q(11,1<<bits),Q(-19,1<<bits)])
        self.assertEqual(physical[0]['modes'][0]['coefficients'],pieces[0]['modes'][0]['coefficients'])


class ReferencePhysicalSourceControls(unittest.TestCase):
    def test_paid_source_full_complex_column_scales_H_bath_capture_shared_APD_and_BG_once(self):
        source,pack=source_fixture();raw=source.record();gamma=Q(raw['reference_clock']['Gamma_numerical_centre'])
        self.assertEqual(raw['same_lambda_aperture_source'],pack['aperture_source'])
        self.assertEqual(raw['same_lambda_aperture_source']['common_optical_source'],pack['common_optical_source'])
        self.assertNotEqual(raw['source_unit_interval'],['1/34500000','1/34500000'])
        ion=code.dipole.ION;g=code.dipole.INDEX[code.dipole.State('ground',1,0)]
        e=code.dipole.INDEX[code.dipole.State('D2',1,0)]
        for key in ((0,code.joint.atom_pair_index(ion,ion),code.joint.atom_pair_index(ion,ion)),
                    (0,code.joint.atom_pair_index(g,e),code.joint.atom_pair_index(e,g))):
            normal=code._read_counter(source.action_column(key,physical=False))
            physical=code._read_counter(source.action_column(key,physical=True))
            self.assertEqual(physical,code._scale(normal,gamma))
            self.assertFalse(sum((v for (c,i,j),v in physical.items() if i==j),code.ZERO))
        physical=code._PhysicalSource(raw)
        # Scalar multiplication uses the already source-generated GKSL
        # products.  No sqrt(Gamma) or integer factorization is requested.
        with patch.object(code.dipole,'sqrt_rational',side_effect=AssertionError('sqrt Gamma must not be formed')):
            column=physical.action({(0,1088,1088):code.dipole.ComplexRadical(1)})
        self.assertTrue(column)
        captured=[v for (c,i,j),v in column.items() if i==j and i!=1088]
        self.assertTrue(captured)

    def test_raw_physical_PC_time_override_and_source_shaped_rejections(self):
        source,_=source_fixture();raw=source.record();frame=code.native.NativeToneFrame.from_record(raw['normalized_native_assembler'])
        cone=code._read_aperture(raw['same_lambda_aperture_source'])
        changed=code.ReferenceAtomicClockSource(frame,aperture_source=cone,physical_duration_seconds=Q(1,100000000))
        self.assertEqual(changed.record()['source_primitive_input'],raw['source_primitive_input'])
        self.assertEqual(changed.record()['physical_geometry']['physical_seconds']['rolling_APD_window'],'1/25')
        self.assertEqual(changed.normalized_times(Q(120,10**9)),code._clock_bounds(Q(120,10**9),raw['reference_clock']))
        with self.assertRaisesRegex(ValueError,'next PC poll'):
            code.ReferenceAtomicClockSource(frame,aperture_source=cone,physical_duration_seconds=Q(1,10))
        with self.assertRaisesRegex(ValueError,'raw native source'):
            code.ReferenceAtomicClockSource({'Ready':[[1088,1088,1]]},aperture_source=cone,physical_duration_seconds=Q(1,10**12))
        bad=copy.deepcopy(raw);bad['reference_clock']['Gamma_numerical_error']='0'
        with self.assertRaisesRegex(ValueError,'source changed'):
            code.ReferenceAtomicClockSource.from_record(bad)
        with patch.object(code,'_scale',lambda matrix,scale:{}),self.assertRaisesRegex(ValueError,'executed source closure'):
            source.record()
        for name in ('_commute','_frequency'):
            with patch.object(code.native,name,lambda *args:{}),self.assertRaisesRegex(ValueError,'source closure'):
                source.record()

    def test_original_CP_residual_checks_the_complete_physical_endpoint_and_automatic_pi_price(self):
        source,report=certified_fixture();clock=source.record()['reference_clock']
        self.assertGreater(Q(report['reference_pi_generator_payment']),0)
        self.assertEqual(report['old_error_once'],'0')
        self.assertLess(Q(report['global_trace_norm_error']),Q(1,10**20))
        endpoint=code._read_counter(report['physical_counter_endpoint'])
        self.assertEqual({(c,i,j):v.conjugate() for (c,j,i),v in endpoint.items()},endpoint)
        trace=sum((v.real.as_rational() for (c,i,j),v in endpoint.items() if i==j),Q(0))
        self.assertLessEqual(abs(trace-1),Q(report['global_trace_norm_error']))
        self.assertTrue(any(i!=j for (c,i,j) in endpoint))
        self.assertTrue(source.verify(report))
        physical=source.physical_trial(report['checker_normalized_pieces'])
        checked=source.certify(physical,physical_time=True)
        self.assertFalse(checked['physical_input_curve_is_original_time_equivalent_to_checker_curve'])
        self.assertTrue(checked['reported_endpoint_is_checked_reparametrized_curve_not_original_physical_trial_readout'])
        self.assertEqual(checked['exact_physical_checker_curve'],
                         code._exact_physical_pullback(checked['checker_normalized_pieces'],Q(clock['Gamma_numerical_centre']),160))
        bad=copy.deepcopy(report);bad['reference_pi_generator_payment']='0'
        with self.assertRaisesRegex(ValueError,'automatic price changed'):
            source.verify(bad)

    def test_reference_physical_counter_generates_ready_only_at_the_original_poll(self):
        source,certificate=certified_fixture();report=source.first_poll_ready(certificate)
        self.assertTrue(report['source_ready_normalizer']['strictly_positive'])
        self.assertEqual(report['first_poll_joint_error'],certificate['global_trace_norm_error'])
        ready=code.channel._read_input(report['generated_first_ready_poststate'],code.joint.DIMENSION)
        pending=code.channel._read_input(report['first_poll_pending_poststate'],code.joint.DIMENSION)
        summed=dict(ready)
        for address,value in pending.items():
            code.local._add(summed,address,value)
        endpoint={}
        for (c,i,j),value in code._read_counter(certificate['physical_counter_endpoint']).items():
            code.local._add(endpoint,(i,j),value)
        self.assertEqual(summed,endpoint)
        self.assertFalse(report['capture_or_hidden_occupancy_used_as_ready'])
        raw=source.record();frame=code.native.NativeToneFrame.from_record(raw['normalized_native_assembler'])
        early=code.ReferenceAtomicClockSource(frame,aperture_source=code._read_aperture(raw['same_lambda_aperture_source']),
            physical_duration_seconds=Q(1,100000000))
        early_report=early.certify(early.generate_trial(order=32))
        with self.assertRaisesRegex(ValueError,'original physical PC poll'):
            early.first_poll_ready(early_report)
        Path('/tmp/reference-atomic-clock-ready-focused-record.json').write_text(json.dumps({
            'source_record':source.record(),'physical_CP_certificate':certificate,'first_poll_ready_certificate':report},
            sort_keys=True),encoding='utf-8')


if __name__=='__main__':
    unittest.main()
