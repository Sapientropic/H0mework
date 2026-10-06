"""Consume frozen detector inverse and original whole-CS hardware constraints."""
import argparse
from pathlib import Path
import subprocess

import detector_fiber_run as science
import verify as parent
from run import exclusive_json

BASE,ROOT=science.BASE,science.ROOT
SCHEMA='stage10-munich-detector-fiber-evidence/v1'
FIRSTS=('detector-fiber-first.json','detector-fiber-independent-first.json')


def validate(primary,checked,rebuilt):
    parent.require(primary.get('schema')=='stage10-munich-detector-fiber-primary/v1' and
                   checked.get('schema')=='stage10-munich-detector-fiber-independent/v1' and
                   primary.get('version')==checked.get('version')==science.VERSION and
                   primary.get('status')=='generated_whole_cs_micro_hardware_constraints' and
                   checked.get('status')=='certified_whole_cs_micro_hardware_constraints','detector_receipt_identity')
    for report in (primary,checked):
        for key,value in science.scope().items():
            parent.require(type(report.get(key)) is type(value) and report[key]==value,'detector_scope_changed')
        parent.require(all(parent.canonical(report.get(key))==parent.canonical(value) for key,value in rebuilt.items()),
                       'detector_exact_inverse_or_whole_cs_domain_changed')
    return rebuilt


def generate():
    science.source_review()
    import atomic_forward_verify
    admitted=atomic_forward_verify.consume()
    parent.require(admitted['raw_control_atomic_response_certified'] is True and
                   admitted['parent_confidence_budget']=='1/20','detector_paid_atomic_confidence_changed')
    primary,checked=(parent.strict_json(parent.frozen(BASE/name)) for name in FIRSTS)
    commit=primary['freeze_commit']; binding=science.bindings(commit)
    for report,name,role in ((primary,'detector-fiber-attempt.json','primary'),
                             (checked,'detector-fiber-independent-attempt.json','independent')):
        raw=parent.frozen(BASE/name); attempt=parent.strict_json(raw)
        parent.require(report['attempt_sha256']==parent.sha256(raw) and
                       report['freeze_commit']==attempt['freeze_commit']==commit and
                       report['execution_head']==attempt['execution_head'] and
                       report['source_bindings']==attempt['source_bindings']==binding and
                       attempt['implementation']==role,'detector_first_attempt_identity_changed')
        run=subprocess.run(['git','merge-base','--is-ancestor',commit,report['execution_head']],cwd=ROOT,capture_output=True)
        parent.require(run.returncode==0,'detector_science_not_frozen_before_execution')
    parent.require(checked['primary_receipt_sha256']==parent.sha256(parent.frozen(BASE/FIRSTS[0])),
                   'detector_primary_identity_changed')
    rebuilt=science.build(*science.compute_inputs(),'independent')
    validate(primary,checked,rebuilt)
    return {'schema':SCHEMA,'criterion_version':science.VERSION,'evidence_valid':True,
            'status':'certified_complete_detector_inverse_and_whole_cs_micro_hardware_domain',**rebuilt,
            'complete_positive_factor_detector_inverse_certified':True,
            'joint_raw_hardware_box_qualification_certified':True,
            'new_numerical_forward_executions_at_intake':0,'trial_events_read_at_intake':0,
            'source_bindings':[parent.binding(BASE/name) for name in
                               ('criterion-df0001.md','detector_fiber_verify.py','detector-source.json',*FIRSTS)]}


def consume(certificate=None):
    path=BASE/'detector-fiber-verification.json' if certificate is None else Path(certificate)
    report=generate()
    parent.require(parent.canonical(report)==parent.canonical(parent.strict_json(path.read_bytes())),
                   'detector_certificate_changed')
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-only',action='store_true'); parser.add_argument('--certificate',type=Path)
    args=parser.parse_args()
    try:
        result=consume(args.certificate) if args.check_only else generate()
        if not args.check_only:
            parent.require(args.certificate is None,'detector_override_is_consume_only')
            exclusive_json(BASE/'detector-fiber-verification.json',result)
        print(parent.canonical(result)); return 0
    except (OSError,ValueError,KeyError,TypeError,subprocess.SubprocessError) as error:
        print(parent.canonical({'schema':SCHEMA,'evidence_valid':False,'reason':str(error)})); return 1


if __name__=='__main__': raise SystemExit(main())
