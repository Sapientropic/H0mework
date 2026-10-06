"""Read-only physical pulse-image membership and same-law response-fibre intake."""
import argparse
from pathlib import Path
import subprocess

import atomic_forward_independent as atomic_checker
import pulse_realization_run as science
import verify as parent
from run import exclusive_json

BASE,ROOT=science.BASE,science.ROOT
SCHEMA='stage10-munich-pulse-image-evidence/v1'
FIRSTS=('pulse-realization-first.json','pulse-realization-independent-first.json')


def validate(primary,checked,witness):
    parent.require(primary.get('schema')=='stage10-munich-pulse-image-primary/v1' and
                   checked.get('schema')=='stage10-munich-pulse-image-independent/v1' and
                   primary.get('status')=='generated_raw_pulse_image_and_source_realizers' and
                   checked.get('status')=='certified_raw_pulse_image_and_source_realizers','pulse_receipt_identity')
    for report in (primary,checked):
        parent.require(report.get('version')==science.VERSION and report.get('evidence_valid') is True,'pulse_receipt_failed')
        for name,value in science.scope().items():
            parent.require(type(report.get(name)) is type(value) and report[name]==value,'pulse_scope_promoted')
        for name,n in (('atomic_samples_checked',4),('response_intersections_checked',12),
                       ('restriction_coefficient_checks',12288),('role_realizer_domains_checked',32),('original_joint_prefixes_replayed',0)):
            parent.require(type(report.get(name)) is int and report[name]==n,'pulse_check_coverage_changed')
        parent.require(report.get('source_effect_identity_used_for_paid_joint_membership') is True,'pulse_source_transport_absent')
        parent.require(tuple(s['id'] for s in report['samples'])==tuple(n for n,_ in science.SAMPLES),'pulse_sample_coverage_changed')
    for row,other,(name,values) in zip(primary['samples'],checked['samples'],science.SAMPLES):
        raw=[dict(zip(science.atomic.KEYS,values))]
        parent.require(row['raw_pulses']==other['raw_pulses']==raw,'pulse_raw_control_changed')
        science.atomic.validate_intervals(row['response'],primary=True)
        science.atomic.validate_intervals(other['response'],primary=False)
        atomic_checker.verify_intersection(row['response'],other['response'])
        restriction=atomic_checker.verify_restriction(raw[0],row['response']['basis'],row['generator_restrictions'])
        parent.require(other['restriction_check']==restriction,'pulse_generator_restriction_changed')
    rebuilt=science.realizations(primary['samples'],witness,'independent')
    for report in (primary,checked):
        parent.require(all(parent.canonical(report.get(k))==parent.canonical(v) for k,v in rebuilt.items()),
                       'pulse_realizer_or_physical_domain_changed')
    return rebuilt


def generate():
    science.source_review()
    import detector_fiber_verify
    admitted=detector_fiber_verify.consume()
    parent.require(admitted['evidence_valid'] is True,'pulse_paid_joint_membership_rejected')
    primary,checked=(parent.strict_json(parent.frozen(BASE/n)) for n in FIRSTS)
    commit=primary['freeze_commit']; binding=science.bindings(commit)
    for report,name,role in ((primary,'pulse-realization-attempt.json','primary'),
                            (checked,'pulse-realization-independent-attempt.json','independent')):
        raw=parent.frozen(BASE/name); attempt=parent.strict_json(raw)
        parent.require(report['freeze_commit']==attempt['freeze_commit']==commit and
                       report['execution_head']==attempt['execution_head'] and
                       report['source_bindings']==attempt['source_bindings']==binding and
                       report['attempt_sha256']==parent.sha256(raw) and attempt['implementation']==role,
                       'pulse_first_attempt_identity_changed')
        run=subprocess.run(['git','merge-base','--is-ancestor',commit,report['execution_head']],cwd=ROOT,capture_output=True)
        parent.require(run.returncode==0,'pulse_science_not_frozen_before_execution')
    parent.require(checked['primary_receipt_sha256']==parent.sha256(parent.frozen(BASE/FIRSTS[0])),
                   'pulse_primary_identity_changed')
    witness=parent.strict_json(parent.frozen(BASE/'primitive-witness-c0002.json'))
    rebuilt=validate(primary,checked,witness)
    return {'schema':SCHEMA,'criterion_version':science.VERSION,'evidence_valid':True,
            'status':'certified_physical_pulse_image_joint_domain_and_response_fibre' if
                     rebuilt['same_law_distinct_physical_responses_certified'] else
                     'certified_physical_pulse_image_joint_domain' if rebuilt['physical_pulse_image_joint_domain_nonempty_certified'] else
                     'predeclared_physical_pulse_samples_unresolved',
            **science.scope(),**rebuilt,'atomic_samples_checked':4,'response_intersections_checked':12,
            'restriction_coefficient_checks':12288,'whole_response_boxes_used':True,
            'original_joint_membership_consumed_by_exact_effect_identity':True,
            'new_numerical_forward_executions_at_intake':0,'trial_events_read_at_intake':0,
            'source_bindings':[parent.binding(BASE/n) for n in ('criterion-rf0001.md','pulse_realization_verify.py','pulse-source.json',*FIRSTS)]}


def consume(certificate=None):
    result=generate(); path=BASE/'pulse-realization-verification.json' if certificate is None else Path(certificate)
    parent.require(parent.canonical(result)==parent.canonical(parent.strict_json(path.read_bytes())),'pulse_certificate_changed')
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-only',action='store_true'); parser.add_argument('--certificate',type=Path)
    args=parser.parse_args()
    try:
        result=consume(args.certificate) if args.check_only else generate()
        if not args.check_only:
            parent.require(args.certificate is None,'pulse_override_is_consume_only')
            exclusive_json(BASE/'pulse-realization-verification.json',result)
        print(parent.canonical(result)); return 0
    except (OSError,ValueError,TypeError,KeyError,subprocess.SubprocessError) as error:
        print(parent.canonical({'schema':SCHEMA,'evidence_valid':False,'reason':str(error)})); return 1


if __name__=='__main__': raise SystemExit(main())
