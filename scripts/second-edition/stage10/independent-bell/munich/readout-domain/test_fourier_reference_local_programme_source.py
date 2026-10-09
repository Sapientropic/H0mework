"""Sequential source-owned states and complete shared Fourier programmes."""
import copy
from fractions import Fraction as Q
from functools import lru_cache
import importlib.util
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import fourier_reference_local_programme_source as code


def raw_plan(duration=Q(1,100000)):
    drives=[(code.atomic.Drive('pump2to1','east',Q(1,2),0,'sigma-'),
             code.atomic.Drive('pump1to1','west',Q(2,3),0,'pi')),
            (code.atomic.Drive('pump2to1','west',Q(1,2),0,'sigma+'),
             code.atomic.Drive('pump1to1','east',Q(2,3),0,'pi')),
            (code.atomic.Drive('excitation','east',Q(3,4),0,'pi'),)]
    return [[{'kind':'excitation' if j==2 else 'preparation','duration_seconds':str(duration),
              'drives':[d.record() for d in row],'cuts_seconds':['0',str(duration)]}
             for j,row in enumerate(drives)] for side in (0,1)]


@lru_cache(maxsize=1)
def parent_fixture():
    raw=json.loads(Path('/tmp/reference-local-phase-focused-record.json').read_text())
    return code.reference.ReferenceLocalPhaseSource.from_record(raw['source_record'])


@lru_cache(maxsize=1)
def programme_fixture():
    parent=code.reference.ReferenceLocalPhaseSource.with_clock_plans(parent_fixture(),raw_plan())
    return code.FourierReferenceLocalProgrammeSource(parent)


class SequentialSourceControls(unittest.TestCase):
    def test_complete_real_parent_default_and_explicit_raw_plan_override(self):
        programme=programme_fixture();record=programme.record();raw=record['reference_local_parent']
        self.assertTrue(record['complete_preparation_then_excitation_plan'])
        self.assertEqual([len(v) for v in raw['local_factor_inventory']],[5,5])
        self.assertEqual([len(v) for v in raw['source_generated_local_plans']],[3,3])
        alternate=code.reference.ReferenceLocalPhaseSource.with_clock_plans(parent_fixture(),raw_plan(Q(1,50000)))
        changed=code.FourierReferenceLocalProgrammeSource(alternate)
        self.assertNotEqual(changed.record()['reference_local_parent']['source_generated_local_plans'],raw['source_generated_local_plans'])
        self.assertEqual(changed.record()['reference_local_parent']['complete_initial_ready'],raw['complete_initial_ready'])
        with self.assertRaises(ValueError):
            code.FourierReferenceLocalProgrammeSource(type('Lookalike',(),{'record':lambda self:raw})())
        with self.assertRaises(TypeError):
            programme.phase_source(0,raw['local_factor_inventory'][0][0]['factor_id'],phase_index=1)

    def test_next_input_is_actual_checked_coimage_and_price_not_ready_again(self):
        programme=programme_fixture();factor=programme.record()['reference_local_parent']['local_factor_inventory'][0][0]['factor_id']
        first=programme.phase_source(0,factor);raw=first.record()
        zero=[{'duration':raw['source_duration'],'modes':[{'lambda':[0,0],'frequency_word':[0,0],'coefficients':[[]]}]}]
        report=code._FactorPhaseSource.certify(first,zero)
        self.assertGreater(Q(report['trace_norm_error']),0)
        next_source=programme.phase_source(0,factor,[report]);next_raw=next_source.record()
        self.assertEqual(next_raw['phase_index'],1)
        self.assertEqual(next_raw['complete_initial_local_factor'],report['full_local_poststate'])
        self.assertNotEqual(next_raw['complete_initial_local_factor'],raw['complete_initial_local_factor'])
        self.assertEqual(next_raw['factor_upstream_error'],report['trace_norm_error'])
        self.assertEqual(next_raw['verified_preceding_phase_certificate_digests'],[code._digest(report)])
        bad=copy.deepcopy(report);bad['trace_norm_error']='0'
        with self.assertRaises(ValueError):
            programme.phase_source(0,factor,[bad])
        with self.assertRaises(ValueError):
            code._FactorPhaseSource(programme,{},0)

    def test_warm_helpers_and_same_shape_other_factor_predecessor_rejected(self):
        programme=programme_fixture();inventory=programme.record()['reference_local_parent']['local_factor_inventory'][0]
        source=programme.phase_source(0,inventory[0]['factor_id'])
        zero=[{'duration':source.record()['source_duration'],'modes':[{'lambda':[0,0],'frequency_word':[0,0],'coefficients':[[]]}]}]
        report=code._FactorPhaseSource.certify(source,zero)
        with self.assertRaises(ValueError):
            programme.phase_source(0,inventory[1]['factor_id'],[report])
        for name in ('_matrix','_prepare_template','_certify_shared_phase'):
            with patch.object(code,name,lambda *args,**kwargs: {}):
                with self.assertRaisesRegex(ValueError,'closure changed'):
                    code.FourierReferenceLocalProgrammeSource.record(programme)

    def test_shared_complex_templates_match_direct_full_curve_and_pay_source_residual(self):
        programme=programme_fixture();factor=programme.record()['reference_local_parent']['local_factor_inventory'][0][0]['factor_id']
        source=programme.phase_source(0,factor);raw=source.record();mb=60;quantum=1<<mb
        initial=code._matrix(raw['complete_initial_local_factor']);points=sorted(initial)
        templates=[{'duration':raw['source_duration'],'modes':[{'lambda':[0,0],'frequency_word':[0,0],
            'coefficients':[[[i,j,quantum,0]]]}]} for i,j in points]
        weights=[[quantum,quantum],[quantum,-quantum]]
        witness={'template_digest':code._digest(templates),'weights':weights}
        precision=dict(mode_bits=mb,coefficient_bits=160,exponential_bits=160)
        shared=code._certify_shared_phase(source,witness,templates,precision)
        merged={'duration':raw['source_duration'],'modes':[]}
        for template,weight in zip(templates,weights):
            mode=copy.deepcopy(template['modes'][0]);row=mode['coefficients'][0][0]
            row[2],row[3]=weight;merged['modes'].append(mode)
        direct=code._FactorPhaseSource.certify(source,[merged],**precision)
        self.assertEqual(shared['full_local_poststate'],direct['full_local_poststate'])
        self.assertEqual(shared['source_input_join_error'],direct['piece_error_records'][0]['join_error'])
        self.assertGreaterEqual(Q(shared['trace_norm_error']),Q(direct['trace_norm_error']))
        self.assertFalse(shared['mode_or_graph_correctness_assumed'])
        bad=copy.deepcopy(witness);bad['template_digest']='another-phase'
        with self.assertRaises(ValueError):
            code._certify_shared_phase(source,bad,templates,precision)
        zeros={'template_digest':code._digest(templates),'weights':[[0,0] for t in templates]}
        with patch.object(code._SequentialColumns,'action',side_effect=AssertionError('zero term must not invoke G')):
            # A patched action invalidates the executed source; use the real action for
            # the issued checkpoint and inspect its exact zero receipt below.
            with self.assertRaisesRegex(ValueError,'closure changed'):
                code._certify_shared_phase(source,zeros,templates,precision)
        result=code._certify_shared_phase(source,zeros,templates,precision)
        self.assertEqual(result['full_local_poststate'],[])
        self.assertGreater(Q(result['source_input_join_error']),0)
        self.assertTrue(all(x['whole_trial_term_is_exactly_zero'] for x in result['original_template_certificates']))
        tiny={'template_digest':code._digest(templates),'weights':[[1,0],[0,1]]}
        paid=code._certify_shared_phase(source,tiny,templates,precision)
        self.assertGreater(Q(paid['source_CP_endpoint_enclosure_payment']),0)
        self.assertLessEqual(Q(paid['source_CP_endpoint_enclosure_payment']),Q(1,10**10))
        self.assertTrue(all(x['classification']=='CP_endpoint_norm_enclosure' for x in paid['original_template_certificates']))
        self.assertTrue(all('complete_saved_complex_Qend' in x['source_CP_endpoint_certificate'] for x in paid['original_template_certificates']))
        self.assertTrue(paid['full_local_poststate'])


@unittest.skipUnless(importlib.util.find_spec('numpy'),'the untrusted shared writer uses bundled numpy')
class WholeProgrammeControls(unittest.TestCase):
    def test_six_raw_phases_five_terms_complete_pair_and_original_time_mother(self):
        programme=programme_fixture()
        print('six-phase-source-ready',flush=True)
        saved_path=Path('/tmp/fourier-reference-programme-phase-checkpoints/c3389510b42ec599/side-0-untrusted-phase-templates.json')
        saved=[json.loads(saved_path.read_text())['templates'],None] if saved_path.exists() else None
        trials=programme.generate_trials(harmonic_order=4,graph_iterations=24,
            checkpoint_directory='/tmp/fourier-reference-programme-phase-checkpoints',saved_phase_templates=saved)
        Path('/tmp/fourier-reference-programme-untrusted-focused-record.json').write_text(json.dumps({
            'source_record':programme.record(),'untrusted_trials':trials},sort_keys=True))
        print('six-phase-untrusted-witnesses-saved',flush=True)
        report=programme.certify(trials)
        Path('/tmp/fourier-reference-programme-focused-record.json').write_text(json.dumps({
            'source_record':programme.record(),'untrusted_trials':trials,'certificate':report,
            'scope':'same reference Ready and declared full six-phase raw control leaf, not uniquely identified actual hardware'},sort_keys=True))
        print('six-phase-certified-E',float(Q(report['trace_norm_error'])),flush=True)
        self.assertTrue(report['complete_preparation_then_excitation_plan'])
        self.assertEqual(len(report['tensor_terms']),5)
        self.assertEqual([sum(len(x['complete_phase_certificates']) for x in row) for row in report['complete_local_factor_certificates']],[15,15])
        self.assertEqual(report['source_local_elapsed_seconds'],['3/100000','3/100000'])
        origin=Q(report['source_ready_physical_clock_seconds'])
        self.assertEqual(list(map(Q,report['source_local_emission_origins_seconds'])),[origin+Q(3,100000)]*2)
        raw=programme.record()['reference_local_parent']
        self.assertEqual(report['old_error_once'],raw['upstream_trace_norm_error'])
        self.assertEqual(report['native_pending_poststate'],raw['native_pending_poststate'])
        matrix=code.channel._read_input(report['full_pair_endpoint'],33**2)
        self.assertEqual(matrix,code.dipole.matrix_adjoint(matrix))
        self.assertLess(Q(report['trace_norm_error']),Q(1,10000))
        for row in report['complete_local_factor_certificates']:
            for factor in row:
                previous='0'
                for phase in factor['complete_phase_certificates']:
                    self.assertEqual(phase['old_factor_error_once'],previous)
                    previous=phase['trace_norm_error']


if __name__=='__main__':
    unittest.main()
