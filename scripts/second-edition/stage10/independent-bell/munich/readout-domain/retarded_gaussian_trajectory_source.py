"""Source-generated Gaussian/frequency components of the stopped receipt flow.

Rotating both retarded atomic legs removes their common optical carrier from
continuous residuals.  The relative carrier remains in interference words.
After a first receipt only the frame counterflow runs: its physical coimage
is held at the original stopping time, while the full field mother persists.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import retarded_gaussian_bsm_source as retarded
import gaussian_local_density_source as density

field, gaussian, dipole, full, channel, joint, bsm = (retarded.field, retarded.gaussian, retarded.dipole,
    retarded.full, retarded.channel, retarded.joint, retarded.bsm)
SCHEMA = 'stage10-source-retarded-Gaussian-stopped-trajectory/v1'
COMPONENTS = ('quiet', ('drive',0), ('drive',1), ('cross',0,1), ('cross',1,0))
_ISSUED = {}
_RETARDED_CHECK, _DENSITY_CHECK = retarded._CHECK, density._CHECK


def _require(value,message):
    if not value:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__),*(Path(m.__file__) for m in (retarded,density,gaussian,field,dipole,full,channel,joint,bsm)))}


def _key(mark):
    return mark.counts, -1 if mark.receipt is None else mark.receipt


def _inventory(gate):
    seen = {bsm.INITIAL}; queue = [bsm.INITIAL]
    while queue:
        mark = queue.pop()
        if mark.receipt is not None:
            continue
        for port in range(4):
            target = bsm.BSMSource.target(gate,mark,port)
            if target not in seen:
                seen.add(target); queue.append(target)
    return tuple(sorted(seen,key=_key))


def _add(result,matrix,factor=1):
    field._add(result,matrix,factor)


def _mark(result,mark,matrix,factor=1):
    _add(result,{(mark,i,j):v for (i,j),v in matrix.items()},factor)


def _norm(state,bits):
    return sum((bsm._entry_norm(m,bits=bits) for m in state.values()),Q(0))


def _parts_digest(parts):
    return _digest([{'quiet':channel._input_record(k),'drive':channel._input_record(v),
        'jumps':[[str(r),channel._input_record(j)] for r,j in jumps], 'phase_error':str(error)}
        for k,v,jumps,error in parts])


class RetardedGaussianTrajectorySource:
    def __init__(self,law,*,bits=192):
        _CHECK(); field._closed(law); gaussian._precision(bits)
        _require(type(law) is retarded.RetardedGaussianBSMSource,
                 'closed original retarded law required; source columns are generated')
        raw = retarded.RetardedGaussianBSMSource.record(law)
        legs = raw['complete_driven_field_source']['Gaussian_source_legs']
        self._law = law
        self._parts = tuple(density._parts(r,bits) for r in legs)
        self._marks = _inventory(law._gate)
        self._value = {'schema':SCHEMA,'retarded_source':raw,'source_bindings':_bindings(),
            'scalar_bits':bits,'generated_stopped_marks':[{'counts':list(m.counts),'receipt':m.receipt} for m in self._marks],
            'complete_mark_counts_not_binary_coarsened':True,
            'source_components':['quiet','Gaussian A','Gaussian B','D2 interference A-B','D2 interference B-A'],
            'relative_carrier_frequency_preserved':True,'physical_stopped_retarded_coimage_frozen':True,
            'post_receipt_frame_counterflow_only':True,'full_field_and_queue_reset':False,
            'source_scope':'complete source-frequency and Gaussian components; event-time retarded first-receipt coimages',
            'input_state_is_verified_trajectory':False,'controller_advance':False}
        self._seal = _digest(self._value)
        _ISSUED[id(self)] = self._seal,self._parts,self._marks,_parts_digest(self._parts)

    def record(self):
        _CHECK(); field._closed(self); owned = _ISSUED.get(id(self))
        _require(type(self) is RetardedGaussianTrajectorySource and
            set(vars(self)) == {'_law','_parts','_marks','_value','_seal'} and owned is not None and
            self._seal == owned[0] and self._parts is owned[1] and self._marks is owned[2] and
            _parts_digest(self._parts) == owned[3] and
            _digest(self._value) == self._seal and self._value['source_bindings'] == _bindings() and
            retarded.RetardedGaussianBSMSource.record(self._law) == self._value['retarded_source'],
            'original retarded source, full marks or generated trajectory columns changed')
        _require(self._law._groups == retarded._closed_groups(
            self._value['retarded_source']['complete_driven_field_source']), 'executed natural jump groups changed')
        return _copy(self._value)

    def _clock(self,time):
        raw = self._value['retarded_source']; time = full.nonnegative(time)
        g0,g1 = map(Q,raw['gate_seconds'])
        _require(g0<=time<=g1,'stopped trajectory belongs to the fixed original detector gate')
        source = raw['complete_driven_field_source']
        births = tuple(Q(a)+Q(b) for a,b in zip(source['flight_seconds'],source['emission_origins_seconds']))
        return tuple(max(Q(0),time-b) for b in births),tuple(time>=b for b in births)

    def _blocks(self,state):
        blocks = bsm.BSMSource.blocks(self._law._gate,state)
        _require(all(m in self._marks for m in blocks),'only source-generated first-receipt marks are admitted')
        return blocks

    def _counter(self,matrix,active):
        result = {}
        legs = self._value['retarded_source']['complete_driven_field_source']['Gaussian_source_legs']
        for side,on in enumerate(active):
            if on:
                k = {(i,i):dipole.ComplexRadical(0,Q(legs[side]['carrier_angular_frequency_per_second']))
                     for i,s in enumerate(dipole.STATES) if s.family == 'D2'}
                _add(result,joint._operator_left(matrix,side,k))
                _add(result,joint._operator_right(matrix,side,dipole.matrix_adjoint(k)))
        return result

    def _component(self,component,blocks,active):
        result = {}; beta = tuple(map(Q,self._value['retarded_source']['BG_source']['BG_rates_per_second']))
        for mark,matrix in blocks.items():
            if mark.receipt is not None:
                if component == 'quiet':
                    _mark(result,mark,RetardedGaussianTrajectorySource._counter(self,matrix,active))
                continue
            if component == 'quiet':
                for side,on in enumerate(active):
                    if on:
                        k = self._parts[side][0]
                        _mark(result,mark,joint._operator_left(matrix,side,k))
                        _mark(result,mark,joint._operator_right(matrix,side,dipole.matrix_adjoint(k)))
                _mark(result,mark,matrix,-sum(beta,Q(0)))
                for port,rate in enumerate(beta):
                    _mark(result,bsm.BSMSource.target(self._law._gate,mark,port),matrix,rate)
            elif component[0] == 'drive':
                side = component[1]
                if active[side]:
                    k = self._parts[side][1]
                    _mark(result,mark,joint._operator_left(matrix,side,k))
                    _mark(result,mark,joint._operator_right(matrix,side,dipole.matrix_adjoint(k)))
                continue
            for group,rate,modes in self._law._groups:
                for mu,first in modes:
                    for nu,second in modes:
                        if not (active[first[0]] and active[second[0]]):
                            continue
                        cross = group[0] == 'D2' and first[0] != second[0]
                        if (component == 'quiet' and cross) or (component != 'quiet' and
                                not (cross and (first[0],second[0]) == component[1:])):
                            continue
                        image = retarded._recycle(matrix,first,second)
                        _mark(result,mark,image,rate*self._law._loss[nu][mu])
                        for port in range(4):
                            coefficient = rate*self._law._transfer[port][mu]*self._law._transfer[port][nu].conjugate()
                            if coefficient:
                                target = bsm.BSMSource.target(self._law._gate,mark,port)
                                _mark(result,target,image,coefficient)
        return result

    def slice_components(self,start,stop,*,envelope_order=10):
        raw = RetardedGaussianTrajectorySource.record(self); bits = raw['scalar_bits']
        a,b = map(full.nonnegative,(start,stop)); _require(a<b,'positive original detector slice required')
        _,active = RetardedGaussianTrajectorySource._clock(self,a)
        RetardedGaussianTrajectorySource._clock(self,b)
        source = raw['retarded_source']['complete_driven_field_source']
        births = tuple(Q(x)+Q(y) for x,y in zip(source['flight_seconds'],source['emission_origins_seconds']))
        _require(not any(a<x<b for x in births),'partition the actual source activation boundary before residual checking')
        omega = tuple(Q(r['carrier_angular_frequency_per_second']) for r in source['Gaussian_source_legs'])
        descriptors = [{'component':'quiet','exact_frequency_per_second':'0','polynomial_coefficients':['1'],'scalar_tail_error':'0'}]
        for side in (0,1):
            local = max(Q(0),a-births[side])
            coeffs,tail = gaussian._envelope_polynomial(source['Gaussian_source_legs'][side],local,b-a,envelope_order,bits) if active[side] else ([Q(0)],Q(0))
            descriptors.append({'component':['drive',side],'exact_frequency_per_second':'0',
                'polynomial_coefficients':list(map(str,coeffs)),'scalar_tail_error':str(field._price_upper(tail,bits))})
        for side,other in ((0,1),(1,0)):
            w = omega[other]-omega[side]
            angle = -omega[side]*(a-births[side])+omega[other]*(a-births[other])
            phase,price = gaussian._exponential(Q(0),angle,bits)
            descriptors.append({'component':['cross',side,other],'exact_frequency_per_second':str(w),
                'polynomial_coefficients':[list(map(str,phase))],
                'scalar_tail_error':str(field._price_upper(price,bits))})
        return {'source_record':raw,'source_detector_interval_seconds':list(map(str,(a,b))),
                'source_active_legs':list(active),'components':descriptors,
                'natural_recycling_and_original_mark_columns_generated':True}

    def component_action(self,component,state,*,slice_start):
        RetardedGaussianTrajectorySource.record(self)
        component = tuple(component) if isinstance(component,list) else component
        _require(component in COMPONENTS,'component belongs to the source-generated trajectory inventory')
        _,active = RetardedGaussianTrajectorySource._clock(self,slice_start)
        return RetardedGaussianTrajectorySource._component(self,component,RetardedGaussianTrajectorySource._blocks(self,state),active)

    def component_action_and_price(self,component,state,*,slice_start):
        image = RetardedGaussianTrajectorySource.component_action(self,component,state,slice_start=slice_start)
        component = tuple(component) if isinstance(component,list) else component
        bits = self._value['scalar_bits']; blocks = RetardedGaussianTrajectorySource._blocks(self,state)
        _,active = RetardedGaussianTrajectorySource._clock(self,slice_start)
        error = Q(0)
        if component != 'quiet' and component[0] == 'drive' and active[component[1]]:
            pending = {m:x for m,x in blocks.items() if m.receipt is None}
            error = self._parts[component[1]][3]*_norm(pending,bits)
        return image,field._price_upper(error,bits)

    def action(self,time,state):
        raw = RetardedGaussianTrajectorySource.record(self); bits = raw['scalar_bits']
        times,active = RetardedGaussianTrajectorySource._clock(self,time)
        blocks = RetardedGaussianTrajectorySource._blocks(self,state); result = {}; error = Q(0)
        source = raw['retarded_source']['complete_driven_field_source']
        legs = source['Gaussian_source_legs']; omega = tuple(Q(r['carrier_angular_frequency_per_second']) for r in legs)
        for component in COMPONENTS:
            image = RetardedGaussianTrajectorySource._component(self,component,blocks,active)
            if component == 'quiet':
                value,price = (Q(1),Q(0)),Q(0)
            elif component[0] == 'drive':
                side = component[1]; r = legs[side]
                value,price = gaussian._exponential(-(times[side]-Q(r['centre_seconds']))**2/(4*Q(r['sigma_squared_seconds'])),Q(0),bits)
                pending = {m:x for m,x in blocks.items() if m.receipt is None}
                if active[side]:
                    error += self._parts[side][3]*(abs(value[0])+price)*_norm(pending,bits)
            else:
                s,o = component[1:]
                value,price = gaussian._exponential(Q(0),-omega[s]*times[s]+omega[o]*times[o],bits)
            _add(result,image,dipole.ComplexRadical(*value))
            error += price*_norm(RetardedGaussianTrajectorySource._blocks(self,image),bits)
        return result,field._price_upper(error,bits)

    def frame(self,time,state,*,inverse=False):
        raw = RetardedGaussianTrajectorySource.record(self); bits = raw['scalar_bits']
        times,_ = RetardedGaussianTrajectorySource._clock(self,time)
        blocks = RetardedGaussianTrajectorySource._blocks(self,state); result = {}; error = Q(0); phases = {}
        omega = tuple(Q(r['carrier_angular_frequency_per_second']) for r in
                      raw['retarded_source']['complete_driven_field_source']['Gaussian_source_legs'])
        for mark,matrix in blocks.items():
            for (i,j),value in matrix.items():
                rows,cols = divmod(i,full.DIMENSION),divmod(j,full.DIMENSION)
                angle = sum((omega[s]*times[s]*((dipole.STATES[cols[s]].family == 'D2')-
                    (dipole.STATES[rows[s]].family == 'D2')) for s in (0,1)),Q(0))
                if inverse:
                    angle = -angle
                if angle not in phases:
                    phases[angle] = gaussian._exponential(Q(0),angle,bits)
                phase,price = phases[angle]
                _add(result,{(mark,i,j):value*dipole.ComplexRadical(*phase)})
                error += price*bsm._entry_norm({(i,j):value},bits=bits)
        return result,field._price_upper(error,bits)


def _function(value):
    value = getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _signature():
    helpers = (_require,_copy,_digest,_bindings,_key,_inventory,_add,_mark,_norm,_parts_digest,_function,_signature,_check,
        density._parts,retarded.RetardedGaussianBSMSource.record,retarded._recycle,retarded._closed_groups,
        gaussian._envelope_polynomial,gaussian._exponential,gaussian._norm,gaussian._matrix,
        bsm.BSMSource.blocks,bsm.BSMSource.target,bsm._entry_norm,
        joint._operator_left,joint._operator_right,dipole.matrix_adjoint,field._closed,field._price_upper,field._add)
    methods = tuple(_function(v) for v in vars(RetardedGaussianTrajectorySource).values() if callable(v))
    return tuple(map(_function,helpers)),methods,SCHEMA,COMPONENTS


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature() == _EXPECTED and
        retarded._CHECK is _RETARDED_CHECK and density._CHECK is _DENSITY_CHECK,
        'source-generated retarded trajectory components changed')
    _RETARDED_CHECK(); _DENSITY_CHECK()


_CHECK,_SIGNATURE = _check,_signature
_EXPECTED = _signature()
