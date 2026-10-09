"""Untrusted pending curves and analytically integrated receipt counterflow.

The source's post-receipt frame frequencies are retained as exact exponents.
Pending and receipt coordinates stay on the original complete Mark carrier;
the unchanged complete residual checker pays every omitted source flow.
"""
from fractions import Fraction as Q

import numpy as np
import retarded_component_numpy_writer as original

checked, integer, trajectory = original.checked, original.integer, original.trajectory


def _require(value, message):
    if not value:
        raise ValueError(message)


def _sum(states, bits=None):
    if not states:
        return original._State(np.array([],dtype=np.int64),np.array([],dtype=np.complex128))
    keys=np.concatenate([s.keys for s in states]);values=np.concatenate([s.values for s in states])
    if not keys.size:
        return original._State(keys,values)
    order=np.argsort(keys);keys=keys[order];values=values[order]
    starts=np.r_[0,np.flatnonzero(keys[1:]!=keys[:-1])+1]
    keys=keys[starts];values=np.add.reduceat(values,starts)
    if bits is not None:
        values=np.ldexp(np.rint(np.ldexp(values.real,bits)),-bits)+1j*np.ldexp(np.rint(np.ldexp(values.imag,bits)),-bits)
    _require(np.all(np.isfinite(values)), 'finite complete counterflow proposal required')
    keep=values!=0
    return original._State(keys[keep],values[keep])


def _scaled(state, factor):
    return original._State(state.keys,state.values*factor)


def _split(paths, state):
    receipt=paths.absorbed[state.keys//paths.size]
    return (original._State(state.keys[~receipt],state.values[~receipt]),
            original._State(state.keys[receipt],state.values[receipt]))


def _frequencies(paths, state, active):
    raw=paths.source._value['retarded_source']['complete_driven_field_source']
    omega=tuple(Q(leg['carrier_angular_frequency_per_second']) for leg in raw['Gaussian_source_legs'])
    groups={}
    for address in state.keys:
        _, quantum=divmod(int(address),paths.size)
        i,j=divmod(quantum,paths.dimension)
        first=(i//33,i%33);second=(j//33,j%33)
        frequency=sum((omega[s]*(int(original.dipole.STATES[first[s]].family=='D2')-
            int(original.dipole.STATES[second[s]].family=='D2')) for s in (0,1) if active[s]),Q(0))
        groups.setdefault(frequency,[]).append(int(address))
    return groups


def _receipt_modes(paths, initial, forcing, width, active, bits):
    all_keys=_sum([initial,*forcing]).keys
    inventory=_frequencies(paths,original._State(all_keys,np.ones(all_keys.size)),active)
    modes={}
    def add(frequency,degree,state,factor):
        if factor and state.keys.size:
            modes.setdefault(frequency,{}).setdefault(degree,[]).append(_scaled(state,factor))
    for frequency,addresses in inventory.items():
        keys=np.asarray(addresses,dtype=np.int64)
        def restrict(state):
            keep=np.isin(state.keys,keys,assume_unique=True)
            return original._State(state.keys[keep],state.values[keep])
        add(frequency,0,restrict(initial),1)
        for n,state in enumerate(forcing):
            state=restrict(state)
            if not state.keys.size:
                continue
            if frequency==0:
                add(Q(0),n+1,state,float(width/Q(n+1)))
            else:
                # Reuse the existing exact scalar integral.  Whole quantum
                # vectors remain numerical proposals; no scalar price is trusted.
                coefficients=[{} for _ in range(n)]+[{(0,0):(Q(1),Q(0))}]
                integral=checked.fourier._integrate_mode((-1,),coefficients,(frequency,),width)
                for word,polynomial in integral.items():
                    target=(1+word[0])*frequency
                    for degree,matrix in polynomial.items():
                        a,b=matrix.get((0,0),(0,0));add(target,degree,state,complex(float(a),float(b)))
    return {frequency:[_sum(polynomial.get(n,[]),bits) for n in range(max(polynomial)+1)]
            for frequency,polynomial in modes.items()}


def generate_trial(source, initial=None, stop=None, *, start=None, slices=1,
                   order=16, mode_bits=96, envelope_order=10, maximum_count_sum=2, progress=None):
    integer._CHECK()
    _require(type(source) is checked.RetardedReceiptTrajectoryCertificate,
             'closed original continuous source required; a target curve is not input')
    raw=checked.RetardedReceiptTrajectoryCertificate.record(source)
    _require(maximum_count_sum is None or (type(maximum_count_sum) is int and maximum_count_sum>=0),
             'nonnegative numerical count budget or complete override required')
    _require(type(slices) is int and slices>0 and type(order) is int and 0<=order<=63,
             'finite pending polynomial and receipt integral budget required')
    trajectory.gaussian._precision(mode_bits)
    original_input,_,issued=checked.RetardedReceiptTrajectoryCertificate._input(source,initial,0)
    g0,g1=map(Q,raw['stopped_trajectory_source']['retarded_source']['gate_seconds'])
    start=g0 if start is None else original.full.nonnegative(start)
    stop=g1 if stop is None else original.full.nonnegative(stop)
    _require(g0<=start<=stop<=g1 and (not issued or start==g0),'original source input cut required')
    _,pairs,_,_=checked._initial(source._source,original_input,start,mode_bits)
    paths=original._Paths(source._source,pairs,maximum_count_sum,mode_bits);current=paths.input(pairs)
    driven=raw['stopped_trajectory_source']['retarded_source']['complete_driven_field_source']
    births=tuple(Q(a)+Q(b) for a,b in zip(driven['flight_seconds'],driven['emission_origins_seconds']))
    edges=sorted({start+n*(stop-start)/slices for n in range(slices+1)}|{x for x in births if start<x<stop})
    scratch=np.zeros(paths.length,dtype=np.complex128);derivative=np.zeros_like(scratch);pieces=[]
    for origin,end in zip(edges,edges[1:]):
        width=end-origin;active,descriptors=original._scalars(source._source,origin,end,order,envelope_order)
        pending,receipt=_split(paths,current);pending_modes=[pending];forcing=[]
        for degree in range(order+1):
            derivative.fill(0)
            for component,scalars in descriptors:
                scratch.fill(0)
                for j in range(degree+1):paths.add(scratch,pending_modes[degree-j],scalars[j])
                paths.action(component,paths.state(scratch),active,derivative)
            matrix=derivative.reshape(len(paths.global_ids),paths.dimension,paths.dimension)
            matrix+=matrix.conjugate().swapaxes(1,2);matrix*=.5
            next_pending,arrival=_split(paths,paths.state(derivative))
            forcing.append(arrival)
            if degree<order:
                pending_modes.append(_sum([_scaled(next_pending,float(width/Q(degree+1)))],mode_bits))
            if progress is not None:
                progress({'completed_pending_degree':degree,'complete_receipt_forcing_coordinates':int(arrival.keys.size),
                          'source_interval_seconds':[str(origin),str(end)]})
        groups=_receipt_modes(paths,receipt,forcing,width,active,mode_bits)
        groups.setdefault(Q(0),[])
        length=max(len(groups[Q(0)]),len(pending_modes))
        groups[Q(0)]=[_sum(([groups[Q(0)][n]] if n<len(groups[Q(0)]) else [])+
            ([pending_modes[n]] if n<len(pending_modes) else []),mode_bits) for n in range(length)]
        modes=[{'lambda_per_second':['0',str(frequency)],'coefficients':[paths.rows(state,mode_bits) for state in coefficients]}
               for frequency,coefficients in sorted(groups.items())]
        pieces.append({'duration_seconds':str(width),'modes':modes})
        current=_sum([_scaled(state,complex(*map(float,checked.gaussian._exponential(Q(0),frequency*width,mode_bits)[0])))
                      for frequency,coefficients in groups.items() for state in coefficients],mode_bits)
    return {'schema':checked.SCHEMA+'/untrusted-curve','source_record':raw,
        'complete_initial_marked_state':checked._record_state(original_input),'source_issued_input_used':issued,
        'source_detector_interval_seconds':list(map(str,(start,stop))),'mode_bits':mode_bits,
        'pieces':pieces,'writer_correctness_assumed':False}
