"""Independent raw-bath reconstruction of the late adjoint source program."""
from fractions import Fraction as Q
import hashlib
import atomic_dipole as dipole
import fluorescence_channel as channel
import gaussian_atomic_pulse_source as gaussian
import positive_quadrature_rha0038 as quadrature


def require(value,reason):
    if not value:raise ValueError(reason)


def raw_jumps(original):
    field=original['complete_driven_field_source'];groups={};checks=[]
    transfer=[[channel._complex_record(z) for z in row] for row in field['working_common_optical_source']['generated_four_by_six_transfer']]
    for side,leg in enumerate(field['physical_legs']):
        pulse=field['Gaussian_source_legs'][side];h=gaussian._matrix(pulse['complete_static_H_per_second']);loss={}
        require(h==dipole.matrix_adjoint(h) and all(dipole.STATES[i].family==dipole.STATES[j].family for i,j in h),
                'independent static family closure failed')
        for item in leg['original_physical_natural_jumps']:
            rate=Q(item['physical_amplitude_squared_per_second']);group=tuple(item['group'])
            mu=3*side+dipole.Q_COMPONENTS.index(item['q']);j=gaussian._matrix(item['normalized_natural_jump_operator'])
            require(rate>=0 and all(dipole.STATES[i].family=='ground' and dipole.STATES[k].family==group[0] for i,k in j),
                    'independent natural line or ground range changed')
            current=groups.setdefault(group,(rate,{}));require(current[0]==rate and mu not in current[1],'independent bath identity changed')
            current[1][mu]=side,j
            gaussian.field._add(loss,dipole.matrix_product(dipole.matrix_adjoint(j),j),rate)
        require(loss==gaussian._matrix(pulse['complete_natural_R_per_second']),'independent complete natural loss disagrees')
        checks.append({'side':side,'complete_H_entries':len(h),'complete_R_entries':len(loss),
            'physical_natural_jumps':len(leg['original_physical_natural_jumps']),
            'ground_compression_zero_complex_units_covered_per_jump':1025,
            'source_static_family_projectors_commute':True,'complete_natural_loss_reconstructed':True})
    rows=[];same=[[{} for _ in range(4)] for _ in range(2)];width=Q(1,10**9)
    for group,(rate,modes) in sorted(groups.items()):
        for port in range(4):
            operators=[{},{}]
            for mu,(side,j) in modes.items():
                for key,value in j.items():
                    operators[side][key]=operators[side].get(key,dipole.ComplexRadical())+transfer[port][mu]*value
            operators=[{k:v for k,v in m.items() if v} for m in operators]
            rows.append({'group':list(group),'port':port,'physical_rate_per_second':str(rate),
                'local_operators':[channel._input_record(m) for m in operators],
                'local_operator_norm_bounds':[str(gaussian._norm(m,192)) for m in operators]})
            for side,j in enumerate(operators):gaussian.field._add(same[side][port],dipole.matrix_product(dipole.matrix_adjoint(j),j),rate*width)
    return checks,rows,[[channel._input_record(m) for m in side] for side in same]


def verify_program(program,original,completed,grid_record):
    require(program['schema']=='stage10-source-late-free-TP-registered-adjoint/rha0038' and
            program['original_retarded_source']==original,'the same original retarded source is required')
    field=original['complete_driven_field_source'];width=Q(1,10**9)
    checks,rows,same=raw_jumps(original)
    require(checks==program['source_static_block_checks'],'complete source block coverage changed')
    require(rows==program['complete_detected_jump_rows'] and same==program['same_arm_effects_scaled_by_piece_seconds'],
        'independent coherent jump effects disagree')
    mid,stop=map(Q,program['source_late_detector_interval_seconds']);a,b=map(Q,original['gate_seconds'])
    require(mid==(a+b)/2 and stop==b and stop-mid==60*width,'the same original late half gate is required')
    cuts=[mid-Q(f)-Q(o) for f,o in zip(field['flight_seconds'],field['emission_origins_seconds'])]
    require(program['source_late_local_cuts_seconds']==list(map(str,cuts)),'independent retarded cuts disagree')
    require(len(program['paid_late_flow_sources'])==2,'both complete late flow sources required')
    for side,flow in enumerate(program['paid_late_flow_sources']):
        row=next(r for r in completed['rows'] if r['side']==side and r['role']=='late_forward')
        require(hashlib.sha256(channel._canonical(flow).encode()).hexdigest()==row['flow_source_sha256'] and
                flow['original_Gaussian_source']==field['Gaussian_source_legs'][side] and flow['direction']=='forward' and
                list(map(Q,flow['source_interval_seconds']))==[cuts[side],cuts[side]+stop-mid],
                'independent source bank or exact late flow provenance changed')
    clock=field['reference_clock'];centre=Q(clock['Gamma_numerical_centre']);lo,hi=map(Q,clock['angular_Gamma_enclosure_per_second'])
    require(0<lo<=centre<=hi and program['Gamma_rate_scale_interval']==list(map(str,(lo/centre,hi/centre))) and
        Q(program['Gamma_relative_error_upper'])==max(centre-lo,hi-centre)/centre,'same mathematical Gamma family required')
    frequencies={'D1':[],'D2':[]};deltas=[]
    for side,pulse in enumerate(field['Gaussian_source_legs']):
        sigma=Q(pulse['sigma_squared_seconds']);offset=cuts[side]-Q(pulse['centre_seconds'])
        if offset>0:
            value,error=gaussian._exponential(-offset*offset/(4*sigma),Q(0),192)
            integral=2*sigma*(abs(value[0])+error)/offset
        else:
            _,upper=gaussian.full._sqrt(sigma.numerator*sigma.denominator,192);integral=6*upper/sigma.denominator
        d=2*gaussian._norm(gaussian._matrix(pulse['source_raising_operator_per_second']),192)*integral
        require(Q(program['late_full_Gaussian_tail_prices'][side]['no_jump_operator_Duhamel_price_upper'])==d,
                'independent original Gaussian tail price disagrees')
        deltas.append(d*hi/centre)
        h=gaussian._matrix(pulse['complete_static_H_per_second']);i=next(k for k,s in enumerate(dipole.STATES) if s.family=='D1')
        frequencies['D1'].append(h.get((i,i),dipole.ComplexRadical()).real.as_rational())
        frequencies['D2'].append(Q(pulse['carrier_angular_frequency_per_second']))
    require(program['late_source_no_jump_tail_prices_with_Gamma_upper']==list(map(str,deltas)) and
        program['free_TP_vs_full_no_jump_adjoint_price_per_observable_norm']==[str(4*d) for d in deltas],
        'independent free-TP adjoint bridge price disagrees')
    require(program['relative_line_frequencies_per_second']=={line:str(v[0]-v[1]) for line,v in frequencies.items()},
            'the original relative optical frames changed')
    require(program['late_source_operator_errors']==[next(row['whole_uniform_operator_error'] for row in completed['rows']
            if row['side']==side and row['role']=='late_forward') for side in (0,1)],'paid original operator errors changed')
    require(program['quadrature']==grid_record and quadrature.check(grid_record['grid'])==grid_record['checked'],
            'independent complete quadrature changed')
    require(program['source_spectator_reader']=='identity under the complete unital free TP adjoint' and
            program['same_arm_spectator_no_jump_survival_inserted'] is False and
            program['all_physical_natural_baths_retained'] is True and program['source_Gaussian_field_truncated'] is False,
            'the complete natural bath or spectator identity changed')
    return True
