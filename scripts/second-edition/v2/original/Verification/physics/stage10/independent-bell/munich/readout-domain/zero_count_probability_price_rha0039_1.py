"""The same paid receipt activity contracts the zero-count query input error."""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import hashlib
import json
import subprocess

import zero_count_run_rha0039 as original
import retarded_receipt_activity_envelope as activity

source=original.source
HERE,ROOT=original.HERE,original.ROOT
SCHEMA='stage10-source-first-receipt-zero-count-activity-price/rha0039.1'
OWN=('criterion-rha0039.1.md','zero_count_probability_price_rha0039_1.py','test_zero_count_probability_price_rha0039_1.py')
INPUTS=(*original.OWN,*original.INPUTS,'zero-count-bank-first-rha0039.json','first-receipt-probability-first-rha0039.json',
    'retarded-normalizer-first-rha0028.json','retarded_receipt_activity_envelope.py')


def bindings(freeze):
    result=original.bindings(freeze)
    for name in (*OWN,*INPUTS):
        p=HERE/name;relative=p.relative_to(ROOT).as_posix();raw=p.read_bytes()
        source.require(subprocess.check_output(['git','-C',str(ROOT),'show',freeze+':'+relative])==raw,'same-source price changed after freeze: '+name)
        result[relative]=hashlib.sha256(raw).hexdigest()
    return result


def contract(first,cap,retarded_source):
    source.require(first['schema']==source.SCHEMA+'/complete-any-first-receipt-probability' and
        cap['schema']==activity.SCHEMA+'/first-receipt-cap' and
        cap['source_record']['retarded_source_record']==retarded_source,
        'the complete first-receipt query and the same original activity source are required')
    g0,g1=map(Q,retarded_source['gate_seconds'])
    source.require(list(map(Q,first['source_detector_interval_seconds']))==[g0,g1] and
        list(map(Q,cap['receipt_time_restriction_seconds']))==[g0,g1] and Q(cap['input_detector_clock_seconds'])==g0 and
        Q(cap['activity_horizon_seconds'])==g1-g0 and cap['source_record']['fixed_gate_seconds']==retarded_source['gate_seconds'] and
        len(cap['pending_mark_bounds'])==1 and cap['pending_mark_bounds'][0]['original_mark_counts']==[0]*4 and
        cap['pending_mark_bounds'][0]['original_mark_receipt'] is None and cap['pending_mark_bounds'][0]['minimum_future_registered_arrivals']==2,
        'the original empty Mark, full gate and two-arrival query are required')
    bits=cap['source_record']['scalar_bits'];rate=Q(cap['source_record']['source_activity']['registered_total_activity_upper_per_second'])
    expected,arithmetic=activity._poisson_cap(rate*(g1-g0),2,bits)
    source.require(Q(cap['source_Poisson_mean_upper'])==rate*(g1-g0) and
        cap['pending_mark_bounds'][0]['tail_arithmetic']==arithmetic and
        Q(cap['pending_mark_bounds'][0]['first_receipt_instrument_input_contraction_upper'])==expected and
        Q(cap['whole_first_receipt_input_contraction_upper'])==expected and 0<expected<=1,
        'the paid complete source Poisson/activity cap arithmetic changed')
    old=Q(first['old_whole_input_error_once']);new=Q(first['whole_new_effect_and_arithmetic_price']);centre=Q(first['any_first_receipt_mass_centre']);mass=Q(first['source_positive_mass_upper'])
    source.require(min(old,new,mass)>=0 and Q(first['whole_first_receipt_error'])==old+new and
        first['source_event_is_complete_first_receipt'] is True and first['old_input_error_repeated_for_three_no_count_queries'] is False,
        'the original complete query price or input provenance changed')
    price=expected*old+new;interval=max(Q(0),centre-price),min(mass,centre+price)
    prior=list(map(Q,first['physical_any_first_receipt_mass_interval']))
    source.require(prior[0]<=interval[0]<=interval[1]<=prior[1],'activity-priced complete query must refine the accepted original interval')
    return {'schema':SCHEMA,'source_retarded_law_sha256':source.digest(retarded_source),
        'source_detector_interval_seconds':list(map(str,(g0,g1))),'any_first_receipt_mass_centre':str(centre),
        'source_first_receipt_operator_contraction_upper':str(expected),
        'old_whole_input_error_once':str(old),'old_input_error_payment':str(expected*old),
        'whole_new_effect_and_arithmetic_price':str(new),'whole_first_receipt_error':str(price),
        'physical_any_first_receipt_mass_interval':list(map(str,interval)),
        'prior_uncontracted_query_interval':first['physical_any_first_receipt_mass_interval'],
        'strictly_positive_complete_normalizer':interval[0]>0,'same_original_source_and_entire_gate':True,
        'new_curve_or_source_generation':False,'old_error_repeated_per_query':False,
        'specific_Psi_label_probability_claimed':False,'actual_hardware_uniquely_identified':False,'controller_advance':False}


def run(freeze,output):
    bound=bindings(freeze);output=Path(output);output.mkdir(parents=True,exist_ok=False)
    original.write(output/'attempt.json',{'scientific_freeze_commit':freeze,'source_bindings':bound})
    complete=json.loads(original.previous.paid.paid.frozen(HERE/'zero-count-bank-first-rha0039.json'))
    source.require(complete['source_bindings']==original.bindings(complete['scientific_freeze_commit']) and
        complete['complete_query_side_count']==6 and complete['all_registered_accuracy_gates_passed'] is True,
        'the accepted complete six-coflow query is required')
    first=json.loads(original.bank.artifact(complete['source_first_receipt_probability']).read_text())
    source.require(first==json.loads(original.previous.paid.paid.frozen(HERE/'first-receipt-probability-first-rha0039.json')),
                   'the original accepted probability changed')
    parent=json.loads(original.bank.artifact(complete['complete_zero_count_source']).read_text());raw=parent['original_retarded_source']
    normalizer=json.loads(original.previous.paid.paid.frozen(HERE/'retarded-normalizer-first-rha0028.json'))
    source.require(normalizer['source_bindings']=={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in normalizer['source_bindings']} and
        normalizer['whole_first_receipt_strictly_positive'] is True,'the paid original activity/normalizer evidence changed')
    report=json.loads(original.bank.artifact(normalizer['report']).read_text());cap=report['complete_source_activity_cap'];record=cap['source_record']
    source.require(record['source_activity']==activity._facts(raw,record['scalar_bits']) and
        cap['source_bindings']==activity._bindings() and record['source_bindings']==activity._bindings(),
        'the independent original bath, objective, Gamma or Mark activity derivation changed')
    # Both retained source records must be the exact same mother, not a
    # shape-matched interval from another pulse or another optical member.
    result=contract(first,cap,raw)
    result.update({'scientific_freeze_commit':freeze,'source_bindings':bound,
        'accepted_zero_count_bank_sha256':hashlib.sha256((HERE/'zero-count-bank-first-rha0039.json').read_bytes()).hexdigest(),
        'paid_activity_normalizer_sha256':hashlib.sha256((HERE/'retarded-normalizer-first-rha0028.json').read_bytes()).hexdigest(),
        'paid_complete_activity_cap_sha256':source.digest(cap),'complete_source_Gamma_and_activity_rebuilt_independently':True})
    original.write(output/'summary.json',result)
    print(json.dumps({'first_receipt_mass_interval':[float(Q(x)) for x in result['physical_any_first_receipt_mass_interval']],
        'whole_error':float(Q(result['whole_first_receipt_error']))}),flush=True)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--freeze',required=True);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    try:run(args.freeze,args.output)
    except Exception as error:
        if args.output.is_dir() and not (args.output/'failure.json').exists():original.write(args.output/'failure.json',{'schema':SCHEMA+'/failed-attempt',
            'scientific_freeze_commit':args.freeze,'reason':str(error),'actual_hardware_uniquely_identified':False,'controller_advance':False})
        raise
