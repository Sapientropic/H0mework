"""The original raw SI controls retain physical units and source prices."""
import copy
from fractions import Fraction as Q
from functools import lru_cache
import json
from pathlib import Path
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import reference_response_window_source as code


@lru_cache(maxsize=1)
def parent_fixture():
    saved=json.loads(Path('/tmp/reference-joint-receipt-time-source-current-before-integral.json').read_text())
    return code.reference.ReferenceLocalPhaseSource.from_record(
        saved['reference_joint_source']['reference_field_source']['reference_local_parent'])


@lru_cache(maxsize=4)
def source_fixture(settings=(0,1)):
    parent=parent_fixture();unit=parent.record()['working_atomic_owner']['atomic_base']['seconds_per_unit']
    timing=code.response.PublicResponseTiming(seconds_per_unit=unit)
    return code.ReferenceResponseWindowSource(parent,timing,settings=settings)


class ReferenceResponseControls(unittest.TestCase):
    def test_original_paid_controls_preserve_physical_r_c_ion_and_receipt_edges(self):
        source=source_fixture();raw=source.record();physical=source.window_source()
        old=code.window.WindowCEMSource.from_record(raw['original_paid_window_source'])
        u0=old.seconds_per_unit;u=physical.seconds_per_unit
        self.assertNotEqual(u0,u)
        self.assertIsNone(raw['working_atomic_owner']['paid_si_leaf'])
        self.assertEqual(raw['original_relative_CEM_cutoffs_seconds'],['13/20000000','809/1000000000'])
        timing=code.response.PublicResponseTiming.from_record(raw['raw_receipt_timing'])
        for side in (0,1):
            expected=old.waveforms[side][0];actual=physical.waveforms[side][1]
            self.assertEqual(actual.duration*u,expected.duration*u0)
            self.assertEqual(actual.r*(1/u),expected.r*(1/u0));self.assertEqual(actual.c*(1/u),expected.c*(1/u0))
            self.assertEqual(actual.fields_r,expected.fields_r);self.assertEqual(actual.fields_c,expected.fields_c)
            self.assertEqual({s:x/u for s,x in actual.ion_rates.items()},
                             {s:x/u0 for s,x in expected.ion_rates.items()})
            self.assertEqual(actual.gammas,dict(zip(code.full.WIDTHS,map(Q,raw['working_atomic_owner']['atomic_base']['natural_widths']))))
            self.assertEqual(physical.registrations[side].electron_flight*u,old.registrations[side].electron_flight*u0)
            self.assertEqual(physical.registrations[side].ion_flight*u,old.registrations[side].ion_flight*u0)
            self.assertEqual(physical.registrations[side].probabilities,old.registrations[side].probabilities)
            self.assertEqual(physical.logic_deadlines[side],timing.events()[side]['CEM_logic_deadline'])
        self.assertEqual(physical.backgrounds,old.backgrounds)
        self.assertFalse(raw['new_unit_owner_given_old_paid_leaf'])
        with Path('/tmp/reference-response-window-source-focused-record.json').open('x') as handle:
            json.dump(raw,handle,sort_keys=True)

    def test_full_Z_and_Gamma_model_are_issued_once_from_the_same_static_owner(self):
        raw=source_fixture().record();model=raw['source_model_certificate']
        self.assertGreater(Q(model['full_Zeeman_omission_price']),0)
        self.assertGreater(Q(model['reference_Gamma_static_and_natural_price']),0)
        self.assertGreater(Q(model['reference_command_trace_norm_error']),0)
        self.assertEqual(Q(raw['source_model_trace_norm_error']),sum(Q(model[key]) for key in
            ('full_Zeeman_omission_price','reference_Gamma_static_and_natural_price','reference_command_trace_norm_error')))
        gamma=Q(raw['reference_clock']['Gamma_numerical_centre']);hi=Q(raw['reference_clock']['angular_Gamma_enclosure_per_second'][1])
        for price in model['local_prices']:
            t=Q(price['complete_physical_response_duration_seconds']);z=Q(price['source_off_diagonal_Z_norm_upper'])
            self.assertEqual(Q(price['full_Zeeman_omission_price']),2*max(gamma,hi)*t*z)
        self.assertTrue(model['pulse_edges_fixed_in_physical_seconds'])
        self.assertFalse(model['old_input_error_repeated_here'])

    def test_setting_registration_and_public_onset_override_keep_the_same_source(self):
        parent=parent_fixture();original=source_fixture().record()
        unit=original['reference_seconds_per_source_unit'];old=original['original_paid_SI_primitives']['run']
        eta=tuple(Q.from_float(old['raw_parameters'][j]) for j in (9,11))
        timing=code.response.PublicResponseTiming(seconds_per_unit=unit,FPGA_trigger_delay_seconds=13*code.response.NS)
        changed=code.ReferenceResponseWindowSource(parent,timing,settings=(1,0),
            registration_coordinates=((eta[0],0),(0,eta[1])))
        raw=changed.record();source=changed.window_source()
        self.assertEqual(raw['reference_local_parent'],original['reference_local_parent'])
        self.assertEqual(source.registrations[0].probabilities,(1-eta[0],0,eta[0],0))
        self.assertEqual(source.registrations[1].probabilities,(1-eta[1],eta[1],0,0))
        self.assertEqual([Q(a)-Q(b) for a,b in zip(raw['receipt_relative_SI_onsets_seconds'],
                          original['receipt_relative_SI_onsets_seconds'])],[13*code.response.NS]*2)
        self.assertNotEqual(source.waveforms[0][1].fields_r,source_fixture().window_source().waveforms[0][1].fields_r)

    def test_wrong_clock_target_lookalike_and_model_or_actual_method_replacement_rejected(self):
        source=source_fixture();parent=parent_fixture();raw=source.record()
        timing=code.response.PublicResponseTiming(seconds_per_unit=Q(1,34500000))
        with self.assertRaisesRegex(ValueError,'same reference clock'):
            code.ReferenceResponseWindowSource(parent,timing,settings=(0,0))
        with self.assertRaisesRegex(ValueError,'closed reference'):
            code.ReferenceResponseWindowSource(SimpleNamespace(record=lambda:raw['reference_local_parent']),source._timing,settings=(0,0))
        with patch.object(code.ReferenceResponseWindowSource,'record',lambda *args:raw), \
             patch.object(code.ReferenceResponseWindowSource,'window_source',lambda *args:source._source), \
             self.assertRaisesRegex(ValueError,'closure changed'):
            code._CHECK()
        with patch.object(code.transport,'source_for_settings',lambda *args,**kwargs:source._source), \
             self.assertRaisesRegex(ValueError,'closure changed'):
            source.record()
        previous=source._value['source_model_trace_norm_error'];source._value['source_model_trace_norm_error']='0'
        try:
            with self.assertRaisesRegex(ValueError,'model price'):
                source.record()
        finally:
            source._value['source_model_trace_norm_error']=previous
        self.assertEqual(source.record(),raw)


if __name__=='__main__':
    unittest.main()
