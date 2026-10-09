"""Untrusted zero-count primal curves on the source's exact forward clock."""
from fractions import Fraction as Q
from pathlib import Path
import argparse
import gzip
import hashlib
import json
import time
import numpy as np

import zero_count_primal_independent_rha0040 as independent
import chebyshev_density_proposal_rha0032_2 as stepping
import gaussian_density_exponential_writer as actions

SCHEMA='stage10-source-first-receipt-primal-zero-count-flow/rha0040'


def _columns(record):
    columns=independent.Columns(record);coordinates={(i,j) for i,j,_,_ in record['source_initial_rotating_matrix']};pending=list(coordinates)
    for key in pending:
        for name in ('quiet','drive'):
            image,_=columns.column(name,key)
            for following in image:
                if following not in coordinates:coordinates.add(following);pending.append(following)
    coordinates=sorted(coordinates);address={k:i for i,k in enumerate(coordinates)};entries={}
    for name in ('quiet','drive'):
        rows,before,values=[],[],[]
        for key in coordinates:
            image,_=columns.column(name,key)
            for out,(a,b) in image.items():
                rows.append(address[out]);before.append(address[key]);values.append(np.clongdouble(stepping.long_rational(a))+np.clongdouble(1j)*stepping.long_rational(b))
        entries[name]=np.array(rows,dtype=np.int64),np.array(before,dtype=np.int64),np.array(values,dtype=np.clongdouble)
    return coordinates,entries


def propose(handoff,output,*,degree=64,piece_seconds=Q(1,10**9),order=40,
            maximum_step_seconds=Q(1,16*10**9),mode_bits=96,allow_float64=False):
    independent.require(handoff['schema']==SCHEMA+'/handoff' and type(allow_float64) is bool,'issued no-count source handoff required')
    bits=np.finfo(np.longdouble).nmant+1
    independent.require(bits>=64 or allow_float64,'actual zero-count proposal requires64-bit mantissa')
    record=handoff['primal_source'];coordinates,entries=_columns(record);n=len(coordinates);scalar=independent.scalar(record)
    independent.require(type(degree) is int and 1<=degree<=64 and type(order) is int and 1<=order<=64 and
        Q(piece_seconds)>0 and Q(maximum_step_seconds)>0,'bounded original no-count proposal required')
    start,stop=map(Q,record['flow_interval_seconds']);independent.require(start==0<stop,'original forward clock begins at zero')
    initial={(i,j):(Q(a),Q(b)) for i,j,a,b in record['source_initial_rotating_matrix']}
    current=np.array([np.clongdouble(stepping.long_rational(initial.get(k,(0,0))[0]))+np.clongdouble(1j)*stepping.long_rational(initial.get(k,(0,0))[1]) for k in coordinates],dtype=np.clongdouble)
    positions={k:i for i,k in enumerate(coordinates)};adjoints=np.array([positions[j,i] for i,j in coordinates],dtype=np.int64)
    norm=stepping.matrix_norm(entries['quiet'],n)+stepping.matrix_norm(entries['drive'],n)
    step=min(Q(maximum_step_seconds),Q(str(np.longdouble(3)/np.longdouble(norm))) if norm else Q(maximum_step_seconds))
    intervals=[];at=start
    while at<stop:following=min(stop,at+Q(piece_seconds));intervals.append((at,following));at=following
    independent.require(len(intervals)*(degree+1)*n<=12_000_000,'complete no-count curve budget exceeded')
    k=np.arange(degree+1,dtype=np.longdouble);weights=np.ones(degree+1,dtype=np.longdouble);weights[[0,-1]]=.5
    pi=np.longdouble('3.1415926535897932384626433832795028841971693993751')
    nodes=np.clip((1+np.cos(pi*k/degree))/2,0,1)
    transform=(np.longdouble(2)/degree)*np.cos(pi*np.outer(k,k)/degree)*weights[None,:];transform[[0,-1],:]*=.5
    origin=start;width=min(step,stop-origin);coefficients=stepping.taylor(entries['quiet'],entries['drive'],current,scalar,origin,width,order)
    output=Path(output);independent.require(not output.exists(),'original no-count proposal stream is immutable')
    started=time.monotonic();steps=1
    with output.open('xb') as handle,gzip.GzipFile(fileobj=handle,mode='wb',mtime=0) as compressed:
        def write(v):compressed.write((json.dumps(v,sort_keys=True,separators=(',',':'))+'\n').encode())
        write({'schema':SCHEMA+'/untrusted-stream','primal_source_sha256':hashlib.sha256(independent.gaussian.channel._canonical(record).encode()).hexdigest(),
            'flow_interval_seconds':list(map(str,(start,stop))),'piece_count':len(intervals),'curve_degree':degree,'mode_bits':mode_bits,
            'numeric_mantissa_bits':bits,'float64_override':allow_float64,'initial_matrix_is_source_issued':True,'source_factor_id':record['factor_id'],
            'operator_positivity_assumed_from_numerical_centre':False,'writer_correctness_assumed':False})
        for index,(lo,hi) in enumerate(intervals):
            values=np.zeros((degree+1,n),dtype=np.clongdouble);targets=[lo+(hi-lo)*Q(str(node)) for node in nodes]
            for node in reversed(range(degree+1)):
                target=targets[node]
                while target>origin+width:
                    current=stepping.evaluate(coefficients,np.longdouble(1));origin+=width;width=min(step,stop-origin)
                    independent.require(width>0,'nonzero source no-count proposal step required')
                    coefficients=stepping.taylor(entries['quiet'],entries['drive'],current,scalar,origin,width,order);steps+=1
                values[node]=stepping.evaluate(coefficients,stepping.long_rational((target-origin)/width))
            fitted=transform@values;fitted=(fitted+np.conjugate(fitted[:,adjoints]))/2
            write({'duration_seconds':str(hi-lo),'chebyshev_coefficients':[stepping.rows_extended(coordinates,v,mode_bits) for v in fitted]})
            if index%16==0 or index+1==len(intervals):print(json.dumps({'primal_no_count_piece':index+1,'pieces':len(intervals),'query':record['query'],'seconds':time.monotonic()-started}),flush=True)
    return {'schema':SCHEMA+'/untrusted-proposal','primal_source_sha256':hashlib.sha256(independent.gaussian.channel._canonical(record).encode()).hexdigest(),
        'curve':{'path':output.name,'bytes':output.stat().st_size,'sha256':hashlib.sha256(output.read_bytes()).hexdigest()},
        'numeric_mantissa_bits':bits,'float64_override':allow_float64,'piece_count':len(intervals),'coordinate_count':n,
        'source_checked':False,'seconds':time.monotonic()-started}


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--input',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--receipt',type=Path,required=True)
    args=p.parse_args();r=propose(json.loads(args.input.read_text()),args.output)
    with args.receipt.open('x') as f:json.dump(r,f,sort_keys=True);f.write('\n')
