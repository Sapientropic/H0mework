"""The same two source baths advance a complete joint atom to detector time.

The exact signed-Hermitian decomposition retains every joint coherence.
Each factor uses the existing complete Gaussian recycling checker.  This
fixed-time reduced channel supplies the integrand of the receipt-time law;
an interval measure must still integrate its own time-dependent channels.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import retarded_gaussian_bsm_source as retarded
import gaussian_local_density_source as density
import factorized_local_phase_source as factors

field,dipole,full,channel,joint,bsm=(retarded.field,retarded.dipole,retarded.full,
                                  retarded.channel,retarded.joint,retarded.bsm)
SCHEMA='stage10-source-retarded-actual-time-joint-atomic-delay/v1'
_ISSUED={}
_RETARDED_CHECK,_DENSITY_CHECK,_FACTOR_CHECK=retarded._CHECK,density._CHECK,factors._CHECK


def _require(value,message):
    if not value:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__),*(Path(m.__file__) for m in (retarded,density,factors,field,dipole,full,channel,joint,bsm)))}


def _input(matrix):
    matrix=channel._read_input(matrix,joint.DIMENSION) if type(matrix) is list else channel._initial(matrix,joint.DIMENSION)
    _require(matrix==dipole.matrix_adjoint(matrix),'complete Hermitian joint input required')
    inventory,terms=factors._factor_inventory(factors._decompose(matrix))
    return matrix,inventory,terms


class RetardedAtomicDelaySource:
    def __init__(self,law):
        _CHECK();field._closed(law)
        _require(type(law) is retarded.RetardedGaussianBSMSource,'closed same-source retarded law required')
        raw=retarded.RetardedGaussianBSMSource.record(law)
        self._law=law
        self._locals=tuple(density.GaussianLocalDensitySource(pulse) for pulse in law._field._pulses)
        self._value={'schema':SCHEMA,'retarded_source':raw,
            'two_full_Gaussian_density_sources':[s.record() for s in self._locals],
            'local_intervals':'[tau-flight_s-origin_s, tau-origin_s]',
            'complete_joint_coherences_and_natural_recycling':True,
            'fixed_time_atomic_marginal_of_same_source_dilation':True,
            'interval_channel_replaced_by_a_representative_time':False,
            'remaining_field_and_queue_reset':False,
            'numerical_input_is_actual_hardware_member':False,
            'source_bindings':_bindings(),'controller_advance':False}
        self._seal=_digest(self._value);_ISSUED[id(self)]=self._seal,self._law,self._locals

    def record(self):
        _CHECK();field._closed(self)
        _require(type(self) is RetardedAtomicDelaySource and
            set(vars(self))=={'_law','_locals','_value','_seal'} and
            _ISSUED.get(id(self))==(self._seal,self._law,self._locals) and
            _digest(self._value)==self._seal and self._value['source_bindings']==_bindings() and
            retarded.RetardedGaussianBSMSource.record(self._law)==self._value['retarded_source'] and
            [s.record() for s in self._locals]==self._value['two_full_Gaussian_density_sources'],
            'original joint delay source, full baths or executed local density source changed')
        _require(self._law._groups==retarded._closed_groups(self._value['retarded_source']['complete_driven_field_source']),
                 'original resolved natural bath changed')
        return _copy(self._value)

    def local_intervals(self,detector_time):
        raw=RetardedAtomicDelaySource.record(self)
        time=full.nonnegative(detector_time);g0,g1=map(Q,raw['retarded_source']['gate_seconds'])
        _require(g0<=time<=g1,'fixed receipt time belongs to the original detector gate')
        starts=retarded.RetardedGaussianBSMSource.local_times(self._law,time)
        flights=tuple(map(Q,raw['retarded_source']['complete_driven_field_source']['flight_seconds']))
        _require(all(t>=0 for t in starts),'both retarded source legs must be active at the receipt time')
        return tuple((start,start+flight) for start,flight in zip(starts,flights))

    def generate_trial(self,initial,detector_time,*,slices=64,order=32,mode_bits=160,
                       coefficient_bits=192,envelope_order=10,representation='polynomial',krylov_dimension=48):
        raw=RetardedAtomicDelaySource.record(self);matrix,inventory,terms=_input(initial)
        _require(representation in ('polynomial','exponential'), 'named original density proposal representation required')
        if representation=='exponential':
            import gaussian_density_exponential_writer as exponential_writer
        intervals=RetardedAtomicDelaySource.local_intervals(self,detector_time)
        curves=[]
        for source,items,(start,stop) in zip(self._locals,inventory,intervals):
            rows=[]
            for item in items:
                options=dict(start=start,slices=slices,order=order,mode_bits=mode_bits,
                    coefficient_bits=coefficient_bits,envelope_order=envelope_order)
                if representation=='exponential':
                    curve=exponential_writer.generate_trial(source,item['initial_local_matrix'],stop,
                        krylov_dimension=krylov_dimension,**options)
                else:
                    curve=source.generate_trial(item['initial_local_matrix'],stop,**options)
                rows.append({'factor_id':item['factor_id'],'untrusted_curve':curve})
            curves.append(rows)
        return {'schema':SCHEMA+'/untrusted-joint-delay','source_record':raw,
            'complete_initial_joint_matrix':channel._input_record(matrix),'source_factor_inventory':inventory,
            'source_tensor_factor_ids':terms,'physical_detector_seconds':str(full.nonnegative(detector_time)),
            'two_source_intervals_seconds':[list(map(str,p)) for p in intervals],
            'two_factor_curve_inventories':curves,'writer_correctness_assumed':False}

    def certify(self,trial,*,input_error=0,coefficient_bits=192,envelope_order=10):
        raw=RetardedAtomicDelaySource.record(self)
        _require(type(trial) is dict and set(trial)=={'schema','source_record','complete_initial_joint_matrix',
            'source_factor_inventory','source_tensor_factor_ids','physical_detector_seconds',
            'two_source_intervals_seconds','two_factor_curve_inventories','writer_correctness_assumed'} and
            trial['schema']==SCHEMA+'/untrusted-joint-delay' and trial['source_record']==raw and
            trial['writer_correctness_assumed'] is False,'untrusted joint delay must bind the original source')
        initial,inventory,terms=_input(trial['complete_initial_joint_matrix'])
        intervals=RetardedAtomicDelaySource.local_intervals(self,trial['physical_detector_seconds'])
        _require(trial['source_factor_inventory']==inventory and trial['source_tensor_factor_ids']==terms and
            trial['two_source_intervals_seconds']==[list(map(str,p)) for p in intervals],
            'original complete decomposition or physical flight interval changed')
        curves=trial['two_factor_curve_inventories']
        _require(type(curves) is list and len(curves)==2,'two complete source factor curves required')
        endpoints=({},{});reports=[]
        for source,items,rows,(start,stop),cache in zip(self._locals,inventory,curves,intervals,endpoints):
            _require(type(rows) is list and len(rows)==len(items),'every complete Hermitian factor needs its own source curve')
            local_reports=[]
            for item,row in zip(items,rows):
                _require(type(row) is dict and set(row)=={'factor_id','untrusted_curve'} and
                    row['factor_id']==item['factor_id'],'factor curve changed its original identity')
                curve=row['untrusted_curve']
                _require(curve['complete_initial_matrix']==item['initial_local_matrix'] and
                    curve['start_seconds']==str(start) and curve['stop_seconds']==str(stop),
                    'factor curve must propagate the full original input over its actual flight')
                report=source.certify(curve,input_error=0,coefficient_bits=coefficient_bits,envelope_order=envelope_order)
                cache[item['factor_id']]=(channel._read_input(report['complete_physical_endpoint'],full.DIMENSION),
                    Q(report['whole_trace_norm_error']))
                local_reports.append({'factor_id':item['factor_id'],'complete_density_certificate':report})
            reports.append(local_reports)
        result={};new_error=Q(0);payments=[]
        for aid,bid in terms:
            a,ea=endpoints[0][aid];b,eb=endpoints[1][bid]
            na,nb=bsm._entry_norm(a,bits=coefficient_bits),bsm._entry_norm(b,bits=coefficient_bits)
            payment=ea*nb+eb*na+ea*eb
            factors._add(result,factors._tensor(a,b));new_error+=payment
            payments.append({'factor_ids':[aid,bid],'complete_tensor_error':str(field._price_upper(payment,coefficient_bits))})
        inherited=full.nonnegative(input_error)
        return {'schema':SCHEMA+'/checked-joint-delay','source_record':raw,'untrusted_trial':_copy(trial),
            'complete_physical_joint_endpoint':channel._input_record(result),
            'whole_input_trace_norm_error_once':str(inherited),
            'new_two_arm_tensor_error':str(field._price_upper(new_error,coefficient_bits)),
            'whole_trace_norm_error':str(field._price_upper(inherited+new_error,coefficient_bits)),
            'two_complete_local_certificate_inventories':reports,'source_tensor_payments':payments,
            'two_source_intervals_seconds':trial['two_source_intervals_seconds'],
            'physical_detector_seconds':trial['physical_detector_seconds'],
            'complete_1089_joint_matrix_retained':True,'local_factor_positivity_assumed':False,
            'whole_input_error_consumed_once_by_tensor_CPTP':True,'representative_time_interval_measure_asserted':False,
            'actual_hardware_member_asserted':False,'coefficient_bits':coefficient_bits,'envelope_order':envelope_order}

    def verify(self,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/checked-joint-delay',
                 'complete joint atomic delay certificate required')
        expected=RetardedAtomicDelaySource.certify(self,report['untrusted_trial'],
            input_error=report['whole_input_trace_norm_error_once'],coefficient_bits=report['coefficient_bits'],
            envelope_order=report['envelope_order'])
        _require(expected==report,'complete joint endpoint, actual flight curve or paid tensor error changed')
        return expected


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _signature():
    helpers=(_require,_copy,_digest,_bindings,_input,_function,_signature,_check,
        retarded.RetardedGaussianBSMSource.record,retarded.RetardedGaussianBSMSource.local_times,retarded._closed_groups,
        density.GaussianLocalDensitySource.record,density.GaussianLocalDensitySource.generate_trial,
        density.GaussianLocalDensitySource.certify,factors._decompose,factors._factor_inventory,factors._tensor,factors._add,
        bsm._entry_norm,field._closed,field._price_upper,channel._initial,channel._read_input,channel._input_record)
    methods=tuple(_function(v) for v in vars(RetardedAtomicDelaySource).values() if callable(v))
    return tuple(map(_function,helpers)),methods,SCHEMA


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature()==_EXPECTED and
        retarded._CHECK is _RETARDED_CHECK and density._CHECK is _DENSITY_CHECK and factors._CHECK is _FACTOR_CHECK,
        'same-source atomic delay execution changed')
    _RETARDED_CHECK();_DENSITY_CHECK();_FACTOR_CHECK()


_CHECK,_SIGNATURE=_check,_signature
_EXPECTED=_signature()
