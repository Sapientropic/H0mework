"""Complete source residuals for signed Hermitian no-count inlet factors."""
from fractions import Fraction as Q
from pathlib import Path
import gzip
import hashlib
import json
import time

import zero_count_primal_source_rha0040 as source
import zero_count_primal_independent_rha0040 as independent
import zero_count_primal_integer_rha0040 as integer
import zero_count_check_rha0039 as previous
import chebyshev_basis_independent_rha0032 as basis


def certify(flow,path,output,*,envelope_order=20,allow_float64=False,strategy='integer',progress=None):
    source.base.require(type(flow) is source.LocalNoCountPrimalFlow and type(allow_float64) is bool and strategy in ('integer','rational'),
                        'closed source-issued primal flow and explicit residual strategy required')
    raw=flow.record();columns=source.Columns(flow);scalar=independent.scalar(raw);path,output=Path(path),Path(output)
    output.mkdir(parents=True,exist_ok=False);sha=hashlib.sha256(path.read_bytes()).hexdigest()
    finite=basis.check(integer.core.derivative_weights,integer.core.product_weights,2*envelope_order,64)
    current={(i,j):(Q(a),Q(b)) for i,j,a,b in raw['source_initial_rotating_matrix']}
    elapsed=Q(0);error=Q(raw['source_initial_frame_and_quantization_price']);records=[];cross=[];started=time.monotonic()
    with gzip.open(path,'rt') as handle:
        header=json.loads(next(handle));mode_bits=header['mode_bits'];source.gaussian._precision(mode_bits)
        source.base.require(header['schema']==source.SCHEMA+'/untrusted-stream' and header['primal_source_sha256']==source.base.digest(raw) and
            header['flow_interval_seconds']==raw['flow_interval_seconds'] and header['initial_matrix_is_source_issued'] is True and
            header['source_factor_id']==raw['factor_id'] and header['operator_positivity_assumed_from_numerical_centre'] is False and
            header['writer_correctness_assumed'] is False and type(header['piece_count']) is int and header['piece_count']>0 and
            type(header['curve_degree']) is int and 1<=header['curve_degree']<=64 and
            (header['numeric_mantissa_bits']>=64 and header['float64_override'] is False or allow_float64),
            'original source, factor, complete primal curve or arithmetic policy changed')
        for index,line in enumerate(handle):
            source.base.require(index<header['piece_count'],'extra source primal piece')
            value=json.loads(line)
            if strategy=='integer':width,end,price,detail=integer.piece(columns,scalar,value,current,elapsed,mode_bits,envelope_order)
            else:width,end,price=independent.piece(raw,value,current,elapsed,mode_bits,envelope_order);detail={'whole_piece_error':str(price)}
            if index in (0,header['piece_count']//2,header['piece_count']-1):
                w,e,p=independent.piece(raw,value,current,elapsed,mode_bits,envelope_order)
                source.base.require(w==width and e==end and abs(p-price)<=Q(1,1 << 80),'independent primal residual disagrees')
                cross.append({'piece':index+1,'complete_endpoint_exactly_equal':True,'price_difference_below_2pow_minus80':True})
            elapsed+=width;current=end;error+=price;records.append(detail)
            source.base.require(elapsed<=Q(raw['flow_interval_seconds'][1]),'primal curve crossed the original query cut')
            if progress is not None and (index%32==0 or index+1==header['piece_count']):
                progress({'query':raw['query'],'side':raw['side'],'factor_index':raw['factor_index'],'piece':index+1,
                    'pieces':header['piece_count'],'error':float(error),'seconds':time.monotonic()-started})
    source.base.require(elapsed==Q(raw['flow_interval_seconds'][1]) and len(records)==header['piece_count'],'complete original primal interval required')
    norm=Q(raw['initial_entry_norm_upper']);gamma=norm*previous.gamma_price(flow._coflow)
    physical,phase=source.frame(raw,current,Q(raw['source_local_interval_seconds'][1]),bits=raw['coefficient_bits'])
    uniform=error+gamma;total=uniform+phase;relative=None if not norm else total/norm
    result={'schema':source.SCHEMA+'/checked','original_primal_source':raw,'untrusted_stream':{'bytes':path.stat().st_size,'sha256':sha},
        'stream_header':header,'complete_piece_prices':records,'independent_source_prefixes':cross,'independent_finite_basis_check':finite,
        'complete_rotating_endpoint':[[i,j,str(a),str(b)] for (i,j),(a,b) in sorted(current.items())],
        'complete_physical_endpoint':source.channel._input_record({k:source.dipole.ComplexRadical(*z) for k,z in physical.items()}),
        'whole_new_uniform_trace_norm_error':str(source.gaussian.field._price_upper(uniform,raw['coefficient_bits'])),
        'whole_new_endpoint_trace_norm_error':str(source.gaussian.field._price_upper(total,raw['coefficient_bits'])),
        'initial_entry_norm_upper':str(norm),'source_curve_residual_error':str(source.gaussian.field._price_upper(error,raw['coefficient_bits'])),
        'mathematical_Gamma_price':str(gamma),'physical_endpoint_frame_price':str(phase),'registered_relative_accuracy':'1/100000000',
        'registered_accuracy_passed':total==0 if norm==0 else relative<=Q(1,10**8),
        'source_Hermitian_TNI_contraction_used':True,'old_inlet_error_reapplied_per_factor':False,
        'signed_factor_positivity_assumed':False,'first_receipt_flux_generated_here':False,
        'actual_hardware_uniquely_identified':False,'controller_advance':False,'seconds':time.monotonic()-started}
    with (output/'checked-primal.json').open('x') as f:json.dump(result,f,sort_keys=True);f.write('\n')
    return result
