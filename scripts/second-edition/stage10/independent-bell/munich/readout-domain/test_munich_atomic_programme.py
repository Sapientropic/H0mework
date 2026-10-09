"""Common atomic-source controls; no solver, archive or empirical replay."""
import copy
from fractions import Fraction as Q
import unittest
from unittest.mock import patch

import atomic_dipole as dipole
import atomic_full_forward as full
import atom_photon_source as photons
import bsm_retry_source as bsm
import bsm_channel as marked
import fluorescence_channel as channel
import joint_fluorescence_presence as joint
import munich_atomic_programme as code
import stopped_bsm_programme as stopped
import window_cem_source as window


MOMENTS = dict(ground=2,D1=Q(2,3),D2=Q(4,3),nuclear=Q(1,10))
IDENTITY = ((1,0,0),(0,1,0),(0,0,1))
TRANSFERS = ({'east':IDENTITY,'west':IDENTITY},{'east':IDENTITY,'west':IDENTITY})


def atomic_base(*, fields=(Q(3,10),Q(-1,5)), widths=None):
    return code.AtomicBase(dict(ground_split=7,D1_split=2,D2_A=Q(1,3),D2_B=Q(1,7),D1_reference=0,D2_reference=7),
             widths or {key:Q(1) if key[0]=='D1' else Q(9,8) for key in full.WIDTHS},
             magnetic_fields=fields,magnetic_moments=MOMENTS,seconds_per_unit=Q(1,1000),radiation_regime='coherent_q_F')


def native_drives(*, detuning=Q(-1,2)):
    return (code.Drive('cooling','east',Q(3,2),detuning,'sigma+'),
            code.Drive('repump','west',(1,Q(1,3)),0,'sigma-'))


def pump_drives(beam='east',pol='sigma+'):
    return (code.Drive('pump2to1',beam,1,0,pol),code.Drive('pump1to1',beam,2,0,'pi'))


class CommonAtomicProgrammeControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.base=atomic_base()
        cls.programme=code.MunichAtomicProgramme(cls.base,TRANSFERS)

    def test_nonzero_field_generates_full_IJ_mixing_and_shared_distinct_natural_widths(self):
        magnetic=self.base.zeeman(0)
        first=dipole.INDEX[dipole.State('ground',1,0)]
        second=dipole.INDEX[dipole.State('ground',2,0)]
        self.assertEqual(abs(magnetic[first,second].real.as_rational()),Q(3,10)*(2-Q(1,10))/2)
        stretched=dipole.INDEX[dipole.State('ground',2,2)]
        self.assertEqual(magnetic[stretched,stretched].real.as_rational(),Q(3,10)*(1+Q(3,20)))
        self.assertEqual(magnetic,dipole.matrix_adjoint(magnetic))
        self.assertFalse(any(dipole.ION in key for key in magnetic))
        raw=self.base.segment(0,1)
        self.assertEqual(raw.gammas['D1',1],1)
        self.assertEqual(raw.gammas['D2',3],Q(9,8))
        self.assertEqual(raw.ion_rates,dict.fromkeys(full.EXCITED,0))
        self.assertEqual(raw.detunings.keys(),set(dipole.STATES))
        restored=code.AtomicBase.from_record(self.base.record())
        self.assertEqual(restored.zeeman(0),magnetic)

    def test_public_simultaneous_roles_keep_off_resonant_edges_and_original_photon_topology(self):
        phase=self.programme.phase('preparation',0,Q(1,1000),pump_drives())
        raw=phase.programme()
        self.assertEqual(len(raw.tones),2)
        self.assertEqual(raw.tones[1].angular_frequency-raw.tones[0].angular_frequency,7)
        self.assertEqual(raw.base.gammas,self.base.segment(0,1).gammas)
        h=phase.hamiltonian_derivative_at_zero()
        g=dipole.INDEX[dipole.State('ground',1,0)]
        e=dipole.INDEX[dipole.State('D2',0,0)]
        self.assertIn((e,g),h)
        self.assertEqual(h,dipole.matrix_adjoint(h))
        unit={(g,e):dipole.ComplexRadical(0,1),(e,g):dipole.ComplexRadical(0,-1)}
        derivative=phase.action_derivative_at_zero(unit)
        self.assertEqual(derivative,dipole.matrix_adjoint(derivative))
        self.assertEqual(sum((v for (i,j),v in derivative.items() if i==j),code.ZERO),code.ZERO)
        self.assertEqual(code.ROLES['excitation'],('D2',1,0))
        self.assertIn('ground F=1,m=0',photons.model_metadata()['preparation'])

    def test_native_40ms_generates_original_shared_counter_cells_and_pays_both_omissions(self):
        a=self.programme.phase('native',0,Q(1,25),native_drives())
        b=self.programme.phase('native',1,Q(1,25),native_drives())
        broad=a.compile_grid((0,40),bits=96)
        fine=a.compile_grid((0,20,40),bits=96)
        self.assertTrue(a.verify_compilation(fine,bits=96))
        self.assertGreater(Q(broad['omitted_Zeeman_operator_norm_upper']),0)
        for cell in broad['cells']:
            self.assertGreater(Q(cell['original_cell']['cptp_duhamel_trace_norm_error']),0)
            self.assertGreater(Q(cell['Zeeman_trace_norm_error']),0)
            self.assertEqual(Q(cell['total_trace_norm_error']),Q(cell['original_cell']['cptp_duhamel_trace_norm_error'])+Q(cell['Zeeman_trace_norm_error']))
        counters,report=self.programme.native_counter_cells(a,b,(0,20,40),(0,20,40),threshold=1,
                          background_rate=Q(1,100),collection=((Q(1,10),0,0,0,0,Q(1,10)),),bits=96)
        self.assertEqual(len(counters),2)
        self.assertTrue(all(type(counter) is joint.JointCounterGenerator for counter in counters))
        self.assertEqual(sum((counter.duration for counter in counters),Q(0))*Q(self.base.record()['seconds_per_unit']),Q(1,25))
        self.assertIn('do not reset',report['counter_boundary_policy'])
        for counter in counters:
            for source in counter.sources:
                self.assertEqual(source.program.gammas,self.base.segment(0,1).gammas)
        wrong=copy.deepcopy(fine);wrong['cells'][0]['Zeeman_trace_norm_error']='0'
        with self.assertRaisesRegex(ValueError,'compilation certificate mismatch'):
            a.verify_compilation(wrong,bits=96)

    def test_original_pair_phases_BSM_gate_and_explicit_frequency_override(self):
        a=self.programme.phase('excitation',0,Q(1,1000),(code.Drive('excitation','east',1,0,'pi'),))
        b=self.programme.phase('excitation',1,Q(1,1000),(code.Drive('excitation','east',1,0,'pi'),))
        phases,price=self.programme.pair_phases(a,b,(0,1),bits=96)
        self.assertIs(type(phases[0]),stopped.RawPairPhase)
        self.assertGreater(Q(price['additional_Zeeman_price']),0)
        self.assertEqual(phases[0].first.gammas,phases[0].second.gammas)
        gate,report=self.programme.bsm_gate(collection_a=photons.ideal_collection(),collection_b=photons.ideal_collection(),
              efficiencies=(Q(1,2),)*4,background_rates=(Q(1,100),)*4,splitter=photons.balanced_beam_splitter(),bits=96)
        self.assertIs(type(gate),bsm.BSMSource)
        self.assertEqual(gate.duration*gate.seconds_per_unit,Q(120,10**9))
        self.assertGreater(Q(report['source_model_trace_norm_error']),0)
        first=self.programme.phase('native',0,Q(1,25),native_drives())
        override=self.programme.phase('native',0,Q(1,25),native_drives(detuning=Q(-1,4)))
        self.assertEqual(first.hamiltonian_derivative_at_zero(),override.hamiltonian_derivative_at_zero())
        self.assertNotEqual(first.hamiltonian_derivative_at_zero(1),override.hamiltonian_derivative_at_zero(1))

    def test_paid_SI_uses_same_spectrum_bath_and_explicit_magnetic_leaf_not_toy_source(self):
        programme=code.MunichAtomicProgramme.from_paid_run('2016-04-15',TRANSFERS,
                                magnetic_fields=(Q(1,10),Q(-1,10)),magnetic_moments=MOMENTS)
        base=programme.atomic_base()
        source,report=programme.si_window_source((0,1))
        self.assertIs(type(source),window.WindowCEMSource)
        self.assertGreater(Q(report['source_model_trace_norm_error']),0)
        for side in (0,1):
            pulse=source.waveforms[side][0]
            self.assertEqual(pulse.gammas,base.segment(side,1).gammas)
            self.assertEqual(set(pulse.ion_rates.values()),{Q(83,25)})
            self.assertEqual((pulse.r,pulse.c),(dipole.ComplexRadical(1),dipole.ComplexRadical(50)))
        record=programme.record()
        width=base.record();width['natural_widths'][0]='2'
        incompatible=code.AtomicBase(width['spectrum'],dict(zip(full.WIDTHS,width['natural_widths'])),
                      magnetic_fields=width['magnetic_fields'],magnetic_moments=width['magnetic_moments'],
                      seconds_per_unit=width['seconds_per_unit'],radiation_regime=width['radiation_regime'])
        with self.assertRaisesRegex(ValueError,'incompatible widths'):
            code.MunichAtomicProgramme(incompatible,TRANSFERS,paid_si_leaf=record['paid_si_leaf'])
        wrong=copy.deepcopy(record['paid_si_leaf']);wrong['run']['raw_parameters'][0]+=1
        with self.assertRaisesRegex(ValueError,'frozen original controls'):
            code.MunichAtomicProgramme(base,TRANSFERS,paid_si_leaf=wrong)
        zero=code.MunichAtomicProgramme.from_paid_run('2016-04-15',TRANSFERS,
                                     magnetic_fields=(0,0),magnetic_moments=MOMENTS)
        raw,price=zero.si_window_source((0,0))
        expected=code.transport.source_for_settings(record['paid_si_leaf']['run'],
                    full.Segment.from_record(record['paid_si_leaf']['raw_template']),(0,0),geometry=record['paid_si_leaf']['geometry'])
        self.assertEqual(raw.record(),expected.record())
        self.assertEqual(price['local_prices'][0]['Zeeman_trace_norm_error'],'0')

    def test_role_defaults_lookalike_bath_parent_and_warm_helper_controls(self):
        for build in (lambda:code.Drive('cooling','east',1,0,'sigma+'),
                      lambda:code.Drive('pump1to1','east',1,0,'sigma+'),
                      lambda:code.Drive('target_density','east',1,0,'pi'),
                      lambda:self.programme.phase('native',0,Q(1,100),native_drives()),
                      lambda:self.programme.phase('preparation',0,Q(1,1000),(pump_drives()[0],)),
                      lambda:self.programme.phase('preparation',0,Q(1,1000),({'rho':1},))):
            with self.assertRaises((ValueError,TypeError)):
                build()
        schedule=self.programme.pumping_schedule(0,((Q(1,1000),pump_drives()),
                              (Q(1,1000),pump_drives('west','sigma-'))))
        self.assertEqual(len(schedule),2)
        with self.assertRaisesRegex(ValueError,'alternate'):
            self.programme.pumping_schedule(0,((Q(1,1000),pump_drives()),(Q(1,1000),pump_drives())))
        foreign=code.MunichAtomicProgramme(atomic_base(widths={k:Q(3) for k in full.WIDTHS}),TRANSFERS)
        first=self.programme.phase('native',0,Q(1,25),native_drives())
        second=foreign.phase('native',1,Q(1,25),native_drives())
        with self.assertRaisesRegex(ValueError,'same-base'):
            self.programme.native_counter_cells(first,second,(0,40),(0,40),threshold=1,background_rate=0,collection=((0,)*6,))
        original=self.programme.record()
        original['atomic_base']['natural_widths'][0]='99'
        self.assertEqual(self.programme.record()['atomic_base'],self.base.record())
        for module,name,value in ((code,'_zeeman',lambda *a:{}),(code,'_guard',lambda:None),
                                  (code,'ROLES',{**code.ROLES,'repump':('D2',1,3)})):
            with patch.object(module,name,value),self.assertRaisesRegex(ValueError,'execution closure changed'):
                self.programme.record()


def constant_trial(duration,initial):
    quantum=1<<60
    entries=[]
    for (i,j),value in sorted(initial.items()):
        value=dipole.complex_exact(value)
        a,b=value.real.as_rational(),value.imag.as_rational()
        entries.append([0,i,j,int(a*quantum),int(b*quantum)])
    return [{'duration':str(duration),'modes':[{'lambda':[0,0],'coefficients':[entries]}]}]


class CompiledConsumerControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.programme=code.MunichAtomicProgramme(atomic_base(),TRANSFERS)
        ground=dipole.INDEX[dipole.State('ground',1,0)]
        other=dipole.INDEX[dipole.State('ground',2,0)]
        g,h=33*ground+ground,33*other+other
        # A Hermitian nonpositive centre distinguishes trace from the complete
        # norm bound; the checker does not promote it to a physical initial law.
        cls.initial={(g,g):dipole.ComplexRadical(2),(h,h):dipole.ComplexRadical(-1)}
        cls.old=Q(1,7)

    def test_warm_owner_phase_and_gate_flux_callbacks_cannot_replace_model_prices(self):
        owner=self.programme
        drives=(code.Drive('cooling','east',0,Q(-1,2),'sigma+'),code.Drive('repump','west',0,0,'sigma-'))
        a=owner.phase('native',0,Q(1,25),drives)
        b=owner.phase('native',1,Q(1,25),drives)
        args=dict(threshold=1,background_rate=0,collection=((0,)*6,),bits=96)
        source,model=code.MunichAtomicProgramme.native_cell(owner,a,b,(0,40),0,**args)
        original=owner.record()
        false=copy.deepcopy(model)
        false['per_unit_model_delta']={key:'0' for key in false['per_unit_model_delta']}
        fake_compiled={key:{'cells':[false[key+'_cell']]} for key in ('first','second')}
        for value in fake_compiled.values():
            value['cells'][0]['Zeeman_trace_norm_error']='0'
            value['cells'][0]['total_trace_norm_error']='0'
        with patch.object(owner,'record',lambda:original), \
             patch.object(owner,'native_counter_cells',lambda *x,**kw:((source,),fake_compiled)), \
             patch.object(owner,'native_cell',lambda *x,**kw:(source,false)):
            calls=(lambda:code.MunichAtomicProgramme.native_cell(owner,a,b,(0,40),0,**args),
                   lambda:code.MunichAtomicProgramme.verify_native_cell(owner,false),
                   lambda:code.MunichAtomicProgramme.certify_native_cell(owner,a,b,(0,40),0,self.initial,[],
                                  background_rate=0,collection=((0,)*6,)),
                   lambda:code.MunichAtomicProgramme.pair_phases(owner,a,b,(0,40)),
                   lambda:code.MunichAtomicProgramme.certify_pair_cell(owner,a,b,(0,40),0,self.initial,[]),
                   lambda:code.MunichAtomicProgramme.certify_gate(owner,self.initial,[],
                                  collection_a=photons.ideal_collection(),collection_b=photons.ideal_collection(),
                                  efficiencies=(1,)*4,background_rates=(0,)*4,splitter=photons.balanced_beam_splitter()))
            for call in calls:
                with self.assertRaisesRegex(ValueError,'snapshot changed'):
                    call()
        phase_record=a.record()
        with patch.object(a,'record',lambda:phase_record),patch.object(a,'compile_grid',lambda *x,**kw:fake_compiled['first']):
            for call in (lambda:code.MunichAtomicProgramme.native_cell(owner,a,b,(0,40),0,**args),
                         lambda:code.MunichAtomicProgramme.pair_phases(owner,a,b,(0,40)),
                         lambda:code.AtomicPhase.verify_compilation(a,fake_compiled['first'])):
                with self.assertRaisesRegex(ValueError,'snapshot changed'):
                    call()
        for method in ('success_flux','blocks','from_record'):
            with patch.object(bsm.BSMSource,method,lambda *x,**kw:[]):
                with self.assertRaisesRegex(ValueError,'execution closure changed'):
                    code.MunichAtomicProgramme.record(owner)
        restored,price=code.MunichAtomicProgramme.native_cell(owner,a,b,(0,40),0,**args)
        self.assertEqual(restored.record(),source.record())
        self.assertEqual(price,model)
        self.assertGreater(Q(price['per_unit_model_delta']['Zeeman']),0)

    def test_owned_native_factory_and_checker_force_nonzero_model_price_once(self):
        drives=(code.Drive('cooling','east',0,Q(-1,2),'sigma+'),code.Drive('repump','west',0,0,'sigma-'))
        a=self.programme.phase('native',0,Q(1,25),drives)
        b=self.programme.phase('native',1,Q(1,25),drives)
        source,model=self.programme.native_cell(a,b,(0,40),0,threshold=1,background_rate=0,collection=((0,)*6,),bits=96)
        self.assertTrue(self.programme.verify_native_cell(model))
        cert=self.programme.certify_native_cell(a,b,(0,40),0,self.initial,constant_trial(source.duration,self.initial),
                background_rate=0,collection=((0,)*6,),upstream_error=self.old,coefficient_bits=96,exponential_bits=96,compilation_bits=96)
        delta=Q(model['per_unit_model_delta']['total'])
        self.assertGreater(delta,0)
        self.assertEqual(Q(cert['input_trace_norm_upper']),3)
        self.assertEqual(Q(cert['source_model_payment']),3*delta)
        raw=cert['source_certificate']
        self.assertEqual(Q(raw['upstream_trace_norm_error']),self.old+3*delta)
        self.assertEqual(Q(cert['global_trace_norm_error']),self.old+3*delta+Q(cert['source_checker_local_error']))
        self.assertTrue(self.programme.verify_native_certificate(cert))
        for name,value in (('source_model_payment','0'),('before_model_trace_norm_error','0')):
            wrong=copy.deepcopy(cert);wrong[name]=value
            with self.assertRaisesRegex(ValueError,'certificate mismatch'):
                self.programme.verify_native_certificate(wrong)
        wrong=copy.deepcopy(model);wrong['per_unit_model_delta']['Zeeman']='0'
        with self.assertRaisesRegex(ValueError,'model delta mismatch'):
            self.programme.verify_native_cell(wrong)

    def test_pair_native_model_error_and_closed_residual_entrance_pay_Zeeman(self):
        drive=(code.Drive('excitation','east',0,0,'pi'),)
        a=self.programme.phase('excitation',0,Q(1,1000),drive)
        b=self.programme.phase('excitation',1,Q(1,1000),drive)
        phases,model=self.programme.pair_phases(a,b,(0,1),bits=96)
        self.assertEqual(phases[0].model_error,Q(model['additional_Zeeman_price']))
        self.assertGreater(phases[0].model_error,0)
        self.assertEqual(phases[0].origin['common_atomic_owner'],self.programme.record())
        cert=self.programme.certify_pair_cell(a,b,(0,1),0,self.initial,constant_trial(1,self.initial),
                   upstream_error=self.old,coefficient_bits=96,exponential_bits=96,compilation_bits=96)
        self.assertEqual(Q(cert['source_model_payment']),3*phases[0].model_error)
        self.assertEqual(Q(cert['source_certificate']['upstream_trace_norm_error']),self.old+3*phases[0].model_error)
        self.assertTrue(self.programme.verify_pair_certificate(cert))
        wrong=copy.deepcopy(cert);wrong['raw_pair_phase']['model_trace_norm_error']='0'
        with self.assertRaisesRegex(ValueError,'certificate mismatch'):
            self.programme.verify_pair_certificate(wrong)

    def test_full_gate_receipt_time_failure_instrument_pays_old_and_model_once(self):
        args=dict(collection_a=photons.ideal_collection(),collection_b=photons.ideal_collection(),
                  efficiencies=(Q(1,2),)*4,background_rates=(0,)*4,splitter=photons.balanced_beam_splitter())
        source,model=self.programme.bsm_gate(**args,bits=96)
        cert=self.programme.certify_gate(self.initial,constant_trial(source.duration,self.initial),**args,
              upstream_error=self.old,coefficient_bits=96,exponential_bits=96,compilation_bits=96)
        payment=3*Q(model['source_model_trace_norm_error'])
        self.assertGreater(payment,0)
        self.assertEqual(Q(cert['source_model_payment']),payment)
        self.assertEqual(Q(cert['source_certificate']['upstream_trace_norm_error']),self.old+payment)
        self.assertEqual(Q(cert['global_trace_norm_error']),self.old+payment+
                  Q(cert['source_checker_terminal_local_error'])+Q(cert['source_checker_time_local_error']))
        self.assertEqual(len(cert['first_receipt_event_poststates']),4)
        self.assertEqual(cert['first_receipt_event_poststates'],[[],[],[],[]])
        self.assertTrue(cert['gate_end_failure_poststate'])
        self.assertEqual(cert['joint_instrument_source_law']['receipt_latch_edges_checked'],4*len(marked.MARK_INVENTORY))
        self.assertTrue(self.programme.verify_gate_certificate(cert))
        for name,value in (('source_model_payment','0'),('global_trace_norm_error',str(self.old)),
                           ('first_receipt_event_poststates',[cert['gate_end_failure_poststate']]*4)):
            wrong=copy.deepcopy(cert);wrong[name]=value
            with self.assertRaisesRegex(ValueError,'certificate mismatch'):
                self.programme.verify_gate_certificate(wrong)


if __name__=='__main__':
    unittest.main()
