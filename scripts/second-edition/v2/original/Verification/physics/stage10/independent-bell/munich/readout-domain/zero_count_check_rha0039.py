"""Full-source residual checking for the original CP subunital adjoint flow."""
from fractions import Fraction as Q
from pathlib import Path
import gzip
import hashlib
import json
import time

import zero_count_receipt_rha0039 as source
import zero_count_integer_rha0039 as arithmetic
import zero_count_independent_rha0039 as independent
import chebyshev_basis_independent_rha0032 as basis


def physical_endpoint(coflow,matrix):
    raw=coflow.record();at=Q(raw['source_local_interval_seconds'][0]);pulse=raw['original_Gaussian_source'];frequency1=Q(raw['D1_frame_frequency_per_second'])
    frequencies=[frequency1 if s.family=='D1' else Q(pulse['carrier_angular_frequency_per_second']) if s.family=='D2' else Q(0) for s in source.dipole.STATES]
    result={};phases={};price=Q(0)
    for (i,j),z in matrix.items():
        angle=(frequencies[j]-frequencies[i])*at
        if angle not in phases:phases[angle]=source.gaussian._exponential(0,angle,raw['coefficient_bits']) if angle else ((Q(1),Q(0)),Q(0))
        phase,error=phases[angle];result[i,j]=source.gaussian.field._product(phase,z);price+=error*(abs(z[0])+abs(z[1]))
    hermitian=arithmetic.density.fourier._hermitian(result)
    return hermitian,price+arithmetic.density.fourier._difference(result,hermitian)


def gamma_price(coflow):
    raw=coflow.record();pulse=coflow._source._original._field._pulses[raw['side']]
    a,b=map(Q,raw['source_local_interval_seconds']);clock=raw['original_Gaussian_source']['reference_clock']
    centre=Q(clock['Gamma_numerical_centre']);lo,hi=map(Q,clock['angular_Gamma_enclosure_per_second'])
    require=source.require;require(0<lo<=centre<=hi,'original positive mathematical Gamma family required')
    rate=max(centre-lo,hi-centre)/centre
    loss=source.gaussian._norm(source.gaussian._matrix(raw['original_Gaussian_source']['complete_natural_R_per_second']),192)
    return 2*pulse.Gamma_math_price(a,b,bits=raw['coefficient_bits'])+rate*(b-a)*(loss+Q(raw['local_recycle_norm_upper_per_second']))


def certify(coflow,path,output,*,envelope_order=20,allow_float64=False,strategy='integer',progress=None):
    source.require(type(coflow) is source.LocalNoCountCoflow and strategy in ('integer','rational') and type(allow_float64) is bool,
                   'closed original local coflow and explicit residual strategy required')
    raw=coflow.record();columns=source.Columns(coflow);scalar=independent.scalar(raw);path,output=Path(path),Path(output)
    output.mkdir(parents=True,exist_ok=False)
    sha=hashlib.sha256(path.read_bytes()).hexdigest();finite=basis.check(arithmetic.core.derivative_weights,arithmetic.core.product_weights,2*envelope_order,64)
    current={(i,i):(Q(1),Q(0)) for i in range(33)};elapsed=error=Q(0);records=[];cross=[];started=time.monotonic()
    with gzip.open(path,'rt') as handle:
        header=json.loads(next(handle));mode_bits=header['mode_bits'];source.gaussian._precision(mode_bits)
        source.require(header['schema']==source.SCHEMA+'/untrusted-stream' and header['coflow_source_sha256']==source.digest(raw) and
            header['flow_interval_seconds']==raw['flow_interval_seconds'] and header['initial_effect_is_identity'] is True and
            header['operator_positivity_assumed_from_numerical_centre'] is False and header['writer_correctness_assumed'] is False and
            type(header['piece_count']) is int and header['piece_count']>0 and type(header['curve_degree']) is int and 1<=header['curve_degree']<=64 and
            (header['numeric_mantissa_bits']>=64 and header['float64_override'] is False or allow_float64),
            'complete zero-count stream source or arithmetic policy changed')
        for index,line in enumerate(handle):
            source.require(index<header['piece_count'],'extra zero-count coflow piece')
            value=json.loads(line)
            if strategy=='integer':width,end,price,detail=arithmetic.piece(columns,scalar,value,current,elapsed,mode_bits,envelope_order)
            else:width,end,price=independent.piece(raw,value,current,elapsed,mode_bits,envelope_order);detail={'whole_piece_operator_error':str(price),'strategy':'independent rational'}
            if index in (0,header['piece_count']//2,header['piece_count']-1):
                w,e,p=independent.piece(raw,value,current,elapsed,mode_bits,envelope_order)
                source.require(w==width and e==end and abs(p-price)<=Q(1,1 << 80),'independent zero-count source residual disagrees')
                cross.append({'piece':index+1,'complete_endpoint_exactly_equal':True,'price_difference_below_2pow_minus80':True})
            elapsed+=width;error+=price;current=end
            source.require(elapsed<=Q(raw['flow_interval_seconds'][1]),'zero-count curve crossed its original physical clock')
            records.append(detail)
            if progress is not None and (index%16==0 or index+1==header['piece_count']):progress({'query':raw['query'],'side':raw['side'],'piece':index+1,'pieces':header['piece_count'],'error':float(error),'seconds':time.monotonic()-started})
    source.require(len(records)==header['piece_count'] and elapsed==Q(raw['flow_interval_seconds'][1]),'complete no-count source interval required')
    physical,phase=physical_endpoint(coflow,current);gamma=gamma_price(coflow);total=error+gamma+phase
    report={'schema':source.SCHEMA+'/checked-coflow','coflow_source':raw,'untrusted_stream':{'bytes':path.stat().st_size,'sha256':sha},'stream_header':header,
        'complete_piece_prices':records,'independent_finite_basis_check':finite,'independent_source_prefixes':cross,
        'complete_rotating_endpoint':[[i,j,str(a),str(b)] for (i,j),(a,b) in sorted(current.items())],
        'complete_physical_effect':source.channel._input_record({k:source.dipole.ComplexRadical(*z) for k,z in physical.items()}),
        'whole_new_operator_error':str(source.gaussian.field._price_upper(total,raw['coefficient_bits'])),
        'source_curve_residual_error':str(source.gaussian.field._price_upper(error,raw['coefficient_bits'])),
        'mathematical_Gamma_price':str(gamma),'physical_frame_price':str(phase),'registered_operator_accuracy':'1/100000000',
        'registered_accuracy_passed':total<=Q(1,10**8),'CP_subunital_operator_contraction_used':True,
        'input_error_applied_to_effect':False,'operator_positivity_assumed_from_numerical_centre':False,
        'actual_hardware_uniquely_identified':False,'controller_advance':False,'seconds':time.monotonic()-started}
    with (output/'checked-coflow.json').open('x') as f:json.dump(report,f,sort_keys=True);f.write('\n')
    return report
