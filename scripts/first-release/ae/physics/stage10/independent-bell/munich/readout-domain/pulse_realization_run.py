"""Frozen raw-pulse image construction and faithful original-joint realization."""
import argparse
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import subprocess

import atomic_forward_run as atomic
import verify as parent
from run import exclusive_json

BASE,ROOT=parent.BASE,parent.ROOT
VERSION='stage10-munich-pulse-image-rf0001'
MODULE=ROOT/'Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutPulseRealization.lean'
FILES=('criterion-rf0001.md','pulse_realization.py','test_pulse_realization.py',
       'pulse_realization_independent.py','test_pulse_realization_independent.py','pulse_realization_run.py',
       'pulse_realization_verify.py','test_pulse_realization_verify.py','PulseCertification.lean',
       'pulse_certify.py','test_pulse_certify.py','pulse-source.md','pulse-source.json','pulse-certification-first.json')
INPUTS=('primitive-witness-c0002.json','verification.json','detector-fiber-verification.json',
        'detector-certification-first.json','atomic-forward-verification.json','model.py',*atomic.FILES)
SAMPLES=(('tau4_R4',('4','4','25','83/25')),('tau5_R4',('5','4','25','83/25')),
         ('tau4_R5',('4','5','25','83/25')),('tau5_R5',('5','5','25','83/25')))


def scope():
    return {'parent_confidence_budget':'1/20','per_role_detector_model_required':True,
            'shared_detector_identity_certified':False,'actual_hardware_uniquely_identified':False,
            'actual_independent_anchor_inputs_available':False,'actual_click_dictionary_selected':False,
            'actual_axis_identity_certified':False,'nominal_atom_centers_used_as_actual_confidence_box':False,
            'new_confidence_budget_spent':False,'new_empirical_fit_executed':False,'trial_event_files_read':0,
            'old_joint_witness_used_as_actual_exact_law':False,'controller_advance':False}


def bindings(commit):
    out=[]
    for path in [*(BASE/name for name in dict.fromkeys((*FILES,*INPUTS))),MODULE]:
        raw=parent.frozen(path,commit)
        parent.require(raw==parent.frozen(path),'pulse_image_science_changed')
        out.append({'path':str(path.relative_to(ROOT)),'sha256':parent.sha256(raw)})
    return out


def source_review():
    import pulse_certify
    parent.require(pulse_certify.consume()['evidence_valid'] is True,'pulse_realizer_kernel_rejected')
    atomic.source_review()
    report=parent.strict_json(parent.frozen(BASE/'pulse-source.json'))
    parent.require(report['evidence_valid'] is True and report['actual_hardware_uniquely_identified'] is False,
                   'pulse_realizer_source_review_rejected')
    for entry in report['source_bindings']:
        parent.require(parent.sha256(parent.frozen(ROOT/entry['path']))==entry['sha256'],'pulse_source_review_changed')


def realizations(samples,witness,implementation):
    if implementation=='primary':
        import pulse_realization as engine
        from model import Effect
    elif implementation=='independent':
        import pulse_realization_independent as engine
        from detector_fiber_independent import Effect
    else: raise ValueError('Registered pulse realizer required')
    parent.require(tuple(row['run'] for row in witness['runs'])==parent.RUNS,'pulse_original_witness_run_identity')
    result=[]; complete=[]
    for sample in samples:
        def physical(key):
            low,high=map(Q,sample['response'][key]); return (max(Q(0),low),min(Q(1),high))
        runs=[]
        for row in witness['runs']:
            roles=[]
            for side in ('alice','bob'):
                parent.require(type(row['primitive'][side]) is list and len(row['primitive'][side])==2,'pulse_witness_effect_coverage')
                for setting,entry in enumerate(row['primitive'][side]):
                    parent.require(set(entry)=={'mu','u','z'},'pulse_witness_target_table_not_primitive')
                    roles.append({'side':side,'setting':setting,**engine.realize_box(Effect(**entry),physical('p_bright'),physical('p_dark'))})
            runs.append({'run':row['run'],'role_realizers':roles,
                         'original_effects_realized':all(x['whole_response_box_realizes_source_effect'] for x in roles)})
        all_good=all(r['original_effects_realized'] for r in runs)
        result.append({'sample':sample['id'],'runs':runs,'both_original_source_witnesses_realized':all_good})
        if all_good: complete.append(sample)
    separated=[]
    for first,second in combinations(complete,2):
        if engine.responses_separated(first['response'],second['response']):
            separated.append([first['id'],second['id']])
    return {'sample_realization_domains':result,'fully_realizing_samples':[s['id'] for s in complete],
            'separated_fully_realizing_sample_pairs':separated,
            'physical_pulse_image_joint_domain_nonempty_certified':bool(complete),
            'same_law_distinct_physical_responses_certified':bool(separated),
            'role_realizer_domains_checked':len(samples)*8}


def generate(role):
    source_review()
    import detector_fiber_verify
    parent.require(detector_fiber_verify.consume()['evidence_valid'] is True,'pulse_old_source_joint_chain_rejected')
    witness=parent.strict_json(parent.frozen(BASE/'primitive-witness-c0002.json'))
    samples=[]
    if role=='primary':
        import atomic_forward as engine
        for name,values in SAMPLES:
            pulse=engine.Pulse(*values); response=engine.propagate((pulse,))
            atomic.validate_intervals(response,primary=True)
            restrictions=engine.generator_coefficients(pulse)
            samples.append({'id':name,'raw_pulses':[dict(zip(atomic.KEYS,values))],'response':response,
                            'generator_restrictions':[[[j,list(map(str,c))] for j,c in row] for row in restrictions]})
        report=realizations(samples,witness,role)
    else:
        import atomic_forward_independent as engine
        primary=parent.strict_json(parent.frozen(BASE/'pulse-realization-first.json'))
        parent.require(primary['schema']=='stage10-munich-pulse-image-primary/v1' and primary['evidence_valid'] is True,
                       'pulse_primary_failed')
        parent.require(tuple(s['id'] for s in primary['samples'])==tuple(n for n,_ in SAMPLES),'pulse_sample_coverage_changed')
        for sample,(name,values) in zip(primary['samples'],SAMPLES):
            raw=[dict(zip(atomic.KEYS,values))]
            parent.require(sample['raw_pulses']==raw,'pulse_raw_controls_changed')
            restrictions=engine.verify_restriction(raw[0],sample['response']['basis'],sample['generator_restrictions'])
            response=engine.propagate(raw)
            atomic.validate_intervals(response,primary=False); engine.verify_intersection(sample['response'],response)
            samples.append({'id':name,'raw_pulses':raw,'response':response,'restriction_check':restrictions})
        # Source realizer domains are checked against the identical primary
        # response boxes. The independent propagation certifies their enclosure.
        report=realizations(primary['samples'],witness,role)
        parent.require(all(primary[key]==value for key,value in report.items()),'pulse_independent_realizer_changed')
        report['primary_receipt_sha256']=parent.sha256(parent.frozen(BASE/'pulse-realization-first.json'))
    return {'schema':'stage10-munich-pulse-image-'+role+'/v1','version':VERSION,'evidence_valid':True,
            'status':'generated_raw_pulse_image_and_source_realizers' if role=='primary' else 'certified_raw_pulse_image_and_source_realizers',
            **scope(),**report,'samples':samples,'atomic_samples_checked':4,'response_intersections_checked':12,
            'restriction_coefficient_checks':12288,'original_joint_prefixes_replayed':0,
            'source_effect_identity_used_for_paid_joint_membership':True}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--freeze-commit',required=True); parser.add_argument('--implementation',choices=('primary','independent'),required=True)
    args=parser.parse_args(); role=args.implementation; suffix='' if role=='primary' else '-independent'
    attempt,first=(BASE/('pulse-realization'+suffix+ending+'.json') for ending in ('-attempt','-first'))
    try:
        parent.require(not attempt.exists() and not first.exists(),'pulse_image_first_already_reserved')
        def git(*argv):
            run=subprocess.run(['git',*argv],cwd=ROOT,text=True,capture_output=True)
            parent.require(run.returncode==0,'pulse_image_freeze_not_ancestor'); return run.stdout.strip()
        commit=git('rev-parse','--verify',args.freeze_commit+'^{commit}'); head=git('rev-parse','HEAD')
        git('merge-base','--is-ancestor',commit,head); binding=bindings(commit)
        exclusive_json(attempt,{'version':VERSION,'implementation':role,'freeze_commit':commit,'execution_head':head,
                                'source_bindings':binding,'trial_event_files_read':0})
    except (OSError,ValueError,KeyError,TypeError) as error:
        print(parent.canonical({'status':'not_started','reason':str(error)})); return 2
    try: report=generate(role)
    except Exception as error:
        report={'status':'execution_failed','evidence_valid':False,'reason':str(error),'error_type':type(error).__name__}
    report.update(freeze_commit=commit,execution_head=head,source_bindings=binding,attempt_sha256=parent.sha256(attempt.read_bytes()))
    exclusive_json(first,report); print(parent.canonical({'status':report['status'],'evidence_valid':report['evidence_valid']}))
    return 0 if report['evidence_valid'] else 1


if __name__=='__main__': raise SystemExit(main())
