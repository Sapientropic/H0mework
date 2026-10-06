"""Frozen whole-CS micro-hardware constraints, without new fitting or propagation."""
import argparse
from fractions import Fraction as Q
from pathlib import Path
import subprocess

import verify as parent
from run import exclusive_json

BASE, ROOT=parent.BASE,parent.ROOT
VERSION='stage10-munich-detector-fiber-df0001'
MODULE=ROOT/'Lean/SaturationMonoid/PhysicsCore/Stage10/Bell/ReadoutDetectorFiber.lean'
FILES=('criterion-df0001.md','detector_fiber.py','test_detector_fiber.py','detector_fiber_independent.py',
       'test_detector_fiber_independent.py','detector_fiber_run.py','detector_fiber_verify.py','test_detector_fiber_verify.py',
       'DetectorCertification.lean','detector_certify.py','test_detector_certify.py',
       'detector-source.md','detector-source.json','detector-certification-first.json')
INPUTS=('shared-response-first.json','identification-first.json','joint-response-first.json',
        'atomic-forward-first.json','atomic-forward-verification.json','joint-response-verification.json',
        'model.py','atomic_dose.py')


def scope():
    return {'whole_parent_confidence_hardware_constraints_certified':True,'parent_confidence_budget':'1/20',
            'click_polarity_selected':False,'actual_hardware_uniquely_identified':False,
            'actual_independent_anchor_inputs_available':False,'all_legal_atomic_effects_pulse_realized':False,
            'new_confidence_budget_spent':False,'new_empirical_fit_executed':False,
            'new_numerical_forward_executions':0,'trial_event_files_read':0,'controller_advance':False}


def bindings(commit):
    out=[]
    for path in [*(BASE/name for name in (*FILES,*INPUTS)),MODULE]:
        raw=parent.frozen(path,commit)
        parent.require(raw==parent.frozen(path),'detector_science_changed')
        out.append({'path':str(path.relative_to(ROOT)),'sha256':parent.sha256(raw)})
    return out


def compute_inputs():
    return [parent.strict_json(parent.frozen(BASE/name)) for name in
            ('shared-response-first.json','identification-first.json','joint-response-first.json','atomic-forward-first.json')]


def build(shared,bias,joint,atomic,implementation):
    if implementation=='primary':
        import detector_fiber as engine
    elif implementation=='independent':
        import detector_fiber_independent as engine
    else:
        raise ValueError('Registered implementation required')
    parent.require(tuple(r['run'] for r in shared['runs'])==tuple(r['run'] for r in bias['runs'])==
                   tuple(r['run'] for r in joint['runs'])==parent.RUNS,'detector_original_run_identity')
    parent.require(tuple(s['id'] for s in atomic['samples'])==('no_readout','weak_readout','response_0','response_1'),
                   'detector_atomic_control_coverage')
    runs=[]
    for old,biased,capped in zip(shared['runs'],bias['runs'],joint['runs']):
        record=engine.confidence_domain(old,biased,capped)
        polygons=[]
        for sample in atomic['samples']:
            response=sample['response']
            def physical(name):
                lo,hi=map(Q,response[name]); return (max(Q(0),lo),min(Q(1),hi))
            for role in record['individual_hardware_constraints']:
                polygons.append({'sample':sample['id'],'side':role['side'],'setting':role['setting'],
                                 **engine.atomic_detector_polygons(role['gain_lower'],role['bias_interval'],
                                                                  physical('p_bright'),physical('p_dark'))})
        controls=[]
        for control in capped['controls']:
            boxes=[]; generated=[]
            for role,cap in zip(record['individual_hardware_constraints'],control['caps']):
                cap=Q(cap); b=Q(role['bias_absolute_upper'])
                area2=Q(4,7)*(2*cap/(1+b+cap))
                rebuilt=engine.hardware_gain_cap(Q(1),area2,b)
                parent.require(rebuilt==cap,'detector_raw_box_cap_not_same_old_source_cap')
                boxes.append({'side':role['side'],'setting':role['setting'],'eta_upper':'1',
                              'area_squared_upper':str(area2),'bias_absolute_upper':str(b)})
                generated.append(str(rebuilt))
            controls.append({'name':control['name']+'_raw_hardware_pullback','raw_hardware_boxes':boxes,
                             'generated_source_gain_caps':generated,'old_joint_profile_status':control['status'],
                             'entire_raw_hardware_box_excluded':control['status']=='entire_lower_orthant_excluded',
                             'profile_pass_used_as_full_physical_membership':False})
        record.update(atomic_response_box_domains=polygons,raw_hardware_joint_controls=controls)
        runs.append(record)
    return {'runs':runs,**scope(),'individual_hardware_constraints_checked':8,'joint_hardware_constraints_checked':6,
            'atomic_response_box_domains_checked':32,'click_polarity_branches_checked':64,
            'raw_hardware_joint_controls_checked':4,'new_joint_profiles_executed':0}


def source_review():
    import detector_certify
    kernel=detector_certify.consume()
    parent.require(kernel.get('evidence_valid') is True,'detector_kernel_not_certified')
    review=parent.strict_json(parent.frozen(BASE/'detector-source.json'))
    parent.require(review.get('evidence_valid') is True and review.get('actual_hardware_uniquely_identified') is False,
                   'detector_source_review_rejected')
    for entry in review['source_bindings']:
        parent.require(parent.sha256(parent.frozen(ROOT/entry['path']))==entry['sha256'],'detector_review_changed')
    return kernel


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--freeze-commit',required=True)
    parser.add_argument('--implementation',choices=('primary','independent'),required=True)
    args=parser.parse_args()
    role=args.implementation; suffix='' if role=='primary' else '-independent'
    attempt,first=(BASE/('detector-fiber'+suffix+ending+'.json') for ending in ('-attempt','-first'))
    try:
        parent.require(not attempt.exists() and not first.exists(),'detector_first_already_reserved')
        def git(*argv):
            run=subprocess.run(['git',*argv],cwd=ROOT,text=True,capture_output=True)
            parent.require(run.returncode==0,'detector_freeze_not_ancestor'); return run.stdout.strip()
        commit=git('rev-parse','--verify',args.freeze_commit+'^{commit}')
        head=git('rev-parse','--verify','HEAD^{commit}')
        git('merge-base','--is-ancestor',commit,head)
        binding=bindings(commit)
        exclusive_json(attempt,{'version':VERSION,'implementation':role,'freeze_commit':commit,'execution_head':head,
                                'source_bindings':binding,'trial_events_read':0})
    except (OSError,ValueError,TypeError,KeyError) as error:
        print(parent.canonical({'status':'not_started','reason':str(error)})); return 2
    try:
        source_review()
        import atomic_forward_verify
        parent.require(atomic_forward_verify.consume()['evidence_valid'] is True,'detector_original_atomic_chain_not_admitted')
        report=build(*compute_inputs(),role)
        if role=='independent':
            primary=parent.strict_json(parent.frozen(BASE/'detector-fiber-first.json'))
            parent.require(primary['status']=='generated_whole_cs_micro_hardware_constraints','detector_primary_failed')
            parent.require(all(report[name]==primary[name] for name in report),'detector_independent_disagreement')
            report['primary_receipt_sha256']=parent.sha256(parent.frozen(BASE/'detector-fiber-first.json'))
        report.update(schema='stage10-munich-detector-fiber-'+role+'/v1',version=VERSION,
                      status='generated_whole_cs_micro_hardware_constraints' if role=='primary' else
                      'certified_whole_cs_micro_hardware_constraints')
    except Exception as error:
        report={'status':'execution_failed','reason':str(error),'error_type':type(error).__name__}
    report.update(freeze_commit=commit,execution_head=head,source_bindings=binding,
                  attempt_sha256=parent.sha256(attempt.read_bytes()))
    exclusive_json(first,report)
    print(parent.canonical({'status':report['status']}))
    return 1 if report['status']=='execution_failed' else 0


if __name__=='__main__': raise SystemExit(main())
