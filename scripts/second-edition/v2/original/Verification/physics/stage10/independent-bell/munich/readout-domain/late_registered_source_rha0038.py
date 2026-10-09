"""The complete original bath generates a late registered adjoint integral.

On the excitation and line-charge blocks the undriven adjoint recycling
vanishes. The actual Gaussian tail is retained through its source Duhamel
price; the spectator identity is transported by the full unital TP adjoint.
"""
from fractions import Fraction as Q
import hashlib
import json

import retarded_gaussian_bsm_source as law
import retarded_receipt_activity_envelope as activity
import gaussian_operator_flow_rha0037_1 as flow
import gaussian_operator_bank_rha0037_1 as bank
import positive_quadrature_rha0038 as quadrature

gaussian,dipole,channel=law.gaussian,law.dipole,law.channel
SCHEMA='stage10-source-late-free-TP-registered-adjoint/rha0038'
PIECE_SECONDS=Q(1,10**9)


def require(value,reason):
    if not value:raise ValueError(reason)


def digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def static_blocks(raw):
    ground={i for i,s in enumerate(dipole.STATES) if s.family=='ground'}
    records=[]
    for side,leg in enumerate(raw['complete_driven_field_source']['Gaussian_source_legs']):
        h=gaussian._matrix(leg['complete_static_H_per_second'])
        r=gaussian._matrix(leg['complete_natural_R_per_second'])
        require(h==dipole.matrix_adjoint(h) and all(dipole.STATES[i].family==dipole.STATES[j].family for i,j in h),
                'the original complete static H must preserve each physical family')
        require(all(i==j and not z.imag and z.real.as_rational()>=0 for (i,j),z in r.items()),
                'the original complete natural R must be diagonal and nonnegative')
        physical=raw['complete_driven_field_source']['physical_legs'][side]
        activity._source_loss(physical,leg['complete_natural_R_per_second'])
        for item in physical['original_physical_natural_jumps']:
            j=gaussian._matrix(item['normalized_natural_jump_operator'])
            require(all(i in ground and dipole.STATES[k].family==item['group'][0] for i,k in j),
                    'every original natural jump must map its excitation line to the ground carrier')
        records.append({'side':side,'complete_H_entries':len(h),'complete_R_entries':len(r),
            'physical_natural_jumps':len(physical['original_physical_natural_jumps']),
            'ground_compression_zero_complex_units_covered_per_jump':33*33-len(ground)**2,
            'source_static_family_projectors_commute':True,
            'complete_natural_loss_reconstructed':True})
    return records


def compile_jumps(source):
    require(type(source) is law.RetardedGaussianBSMSource,'closed original retarded source required; a jump table is not input')
    raw=source.record(); blocks=static_blocks(raw); rows=[]
    for group,rate,modes in source._groups:
        for port in range(4):
            operators=[{},{}]
            for mu,(side,jump) in modes:
                law.field._add(operators[side],jump,source._transfer[port][mu])
            require(all(all(dipole.STATES[i].family=='ground' and dipole.STATES[j].family==group[0]
                        for i,j in operator) for operator in operators),'detected group changed its original line charge')
            rows.append({'group':list(group),'port':port,'physical_rate_per_second':str(rate),
                'local_operators':[channel._input_record(m) for m in operators],
                'local_operator_norm_bounds':[str(gaussian._norm(m,192)) for m in operators]})
    same=[[{} for _ in range(4)] for _ in range(2)]
    for row in rows:
        rate=Q(row['physical_rate_per_second'])
        for side,encoded in enumerate(row['local_operators']):
            j=gaussian._matrix(encoded)
            law.field._add(same[side][row['port']],dipole.matrix_product(dipole.matrix_adjoint(j),j),rate*PIECE_SECONDS)
    require(all(m==dipole.matrix_adjoint(m) and all(dipole.STATES[i].family==dipole.STATES[j].family and
            dipole.STATES[i].family in ('D1','D2') for i,j in m) for side in same for m in side),
            'same-arm jump effects must preserve the complete excitation carrier')
    return raw,blocks,rows,[[channel._input_record(m) for m in side] for side in same]


def source_program(source,late_flows,completed,grid_record):
    raw,blocks,rows,same=compile_jumps(source)
    frozen=json.loads(bank.paid.paid.frozen(bank.HERE/'gaussian-operator-bank-first-rha0037.1.json'))
    require(completed==frozen and completed['source_bindings']==bank.bindings(completed['scientific_freeze_commit']),
            'the accepted operator bank must retain its frozen source bindings')
    require(completed['schema']==bank.SCHEMA+'/checked-bank' and completed['all_registered_accuracy_gates_passed'] is True and
            completed['scientific_freeze_commit']=='491cef8fdf22aa4fab8f768137882fa5c96a6106',
            'the completed six original operator flows are required')
    g0,g1=map(Q,raw['gate_seconds']);mid=(g0+g1)/2
    require(g1-g0==Q(120,10**9) and len(late_flows)==2,'the original full gate and two late source flows required')
    legs=raw['complete_driven_field_source']['Gaussian_source_legs']; cuts=source.local_times(mid)
    frequencies={'D1':[],'D2':[]}; errors=[]; tails=[]
    for side,chosen in enumerate(late_flows):
        require(type(chosen) is flow.GaussianOperatorFlow,'closed original operator flow required')
        rec=chosen.record()
        require(rec['original_Gaussian_source']==legs[side] and rec['direction']=='forward' and
                list(map(Q,rec['source_interval_seconds']))==[cuts[side],cuts[side]+g1-mid],
                'late curve must be the same original arm and detector interval')
        expected=next(r for r in completed['rows'] if r['side']==side and r['role']=='late_forward')
        require(expected['flow_source_sha256']==flow.digest(rec) and expected['registered_accuracy_passed'] is True,
                'the exact original late source has not been checked')
        errors.append(expected['whole_uniform_operator_error'])
        frequencies['D1'].append(Q(rec['D1_frame_frequency_per_second']))
        frequencies['D2'].append(Q(legs[side]['carrier_angular_frequency_per_second']))
        tails.append(chosen._pulse.field_off_tail_price(cuts[side],bits=192))
    clock=raw['complete_driven_field_source']['reference_clock'];centre=Q(clock['Gamma_numerical_centre'])
    lo,hi=map(Q,clock['angular_Gamma_enclosure_per_second']);require(0<lo<=centre<=hi,'same positive Gamma family required')
    deltas=[Q(t['no_jump_operator_Duhamel_price_upper'])*hi/centre for t in tails]
    phases={line:str(values[0]-values[1]) for line,values in frequencies.items()}
    require(all(abs(Q(v)*PIECE_SECONDS)<=1 for v in phases.values()),'refine the phase polynomial before this source integral')
    checked=quadrature.check(grid_record['grid'])
    require(grid_record==json.loads(bank.paid.paid.frozen(bank.HERE/'quadrature-first-rha0038.json')) and
            checked==grid_record['checked'] and checked['registered_accuracy_passed'] is True and
            (grid_record['grid']['points'],grid_record['grid']['degree'],grid_record['grid']['bits'])==(160,296,192),
            'the complete frozen positive quadrature is required')
    basis={line:[[i,j] for i,s in enumerate(dipole.STATES) for j,t in enumerate(dipole.STATES)
                  if s.family==line and t.family=='ground'] for line in ('D1','D2')}
    envelope=activity.RetardedReceiptActivityEnvelope(source,bits=192).record()
    return {'schema':SCHEMA,'original_retarded_source':raw,'original_retarded_source_sha256':digest(raw),
        'source_identity':{'source':'positiveSmoothUnifiedSource','root_visit':10,'material_row':0,'current_tick':16,'next_tick':17},
        'source_late_detector_interval_seconds':list(map(str,(mid,g1))),
        'source_late_local_cuts_seconds':list(map(str,cuts)),'piece_seconds':str(PIECE_SECONDS),'complete_piece_count':60,
        'paid_late_flow_sources':[chosen.record() for chosen in late_flows],
        'source_static_block_checks':blocks,'complete_detected_jump_rows':rows,
        'same_arm_effects_scaled_by_piece_seconds':same,'raised_operator_bases':basis,
        'late_source_operator_errors':errors,'late_full_Gaussian_tail_prices':tails,
        'late_source_no_jump_tail_prices_with_Gamma_upper':list(map(str,deltas)),
        'free_TP_vs_full_no_jump_adjoint_price_per_observable_norm':list(map(lambda d:str(4*d),deltas)),
        'relative_line_frequencies_per_second':phases,'relative_phase_polynomial_order':40,
        'Gamma_rate_scale_interval':list(map(str,(lo/centre,hi/centre))),
        'Gamma_relative_error_upper':str(max(centre-lo,hi-centre)/centre),
        'original_background_rates_per_second':raw['BG_source']['BG_rates_per_second'],
        'registered_total_activity_upper_per_second':envelope['source_activity']['registered_total_activity_upper_per_second'],
        'quadrature':grid_record,'source_spectator_reader':'identity under the complete unital free TP adjoint',
        'same_arm_spectator_no_jump_survival_inserted':False,'source_Gaussian_field_truncated':False,
        'all_physical_natural_baths_retained':True,'old_inlet_error_applied_to_effect':False,
        'full_first_receipt_or_response_anchor_certified':False,'actual_hardware_uniquely_identified':False,'controller_advance':False}
