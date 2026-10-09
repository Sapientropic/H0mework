"""A source-derived uniform price for receipt-dependent physical delays.

Both complete baths are compared in the same physical atomic basis.  The
static Hamiltonian and natural recycling cancel in the Duhamel difference;
the Gaussian translation and its lab carrier phase are both paid.  This
operator bound lets a time-measure consumer price an anchor approximation.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import retarded_atomic_delay_source as delay

field,full,channel,gaussian=delay.field,delay.full,delay.channel,delay.density.gaussian
SCHEMA='stage10-source-uniform-actual-time-atomic-delay-envelope/v1'
_ISSUED={}
_DELAY_CHECK=delay._CHECK


def _require(value,message):
    if not value:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__),*(Path(m.__file__) for m in (delay,gaussian,field,full,channel)))}


def _root_upper(value,bits):
    value=full.nonnegative(value)
    _,hi=full._sqrt(value.numerator*value.denominator,bits)
    return field._price_upper(hi/value.denominator,bits)


def _Gaussian_upper(pulse,start,stop,bits):
    centre=Q(pulse['centre_seconds']);variance=Q(pulse['sigma_squared_seconds'])
    distance=max(Q(0),start-centre,centre-stop)
    value,error=gaussian._exponential(-distance*distance/(4*variance),Q(0),bits)
    return min(Q(1),field._price_upper(value[0]+error,bits))


class RetardedAtomicDelayEnvelope:
    def __init__(self,source,*,bits=192):
        _CHECK();field._closed(source);gaussian._precision(bits)
        _require(type(source) is delay.RetardedAtomicDelaySource,'closed original two-arm atomic delay source required')
        raw=source.record();clock=raw['retarded_source']['complete_driven_field_source']['reference_clock']
        gamma=Q(clock['Gamma_numerical_centre']);lo,hi=map(Q,clock['angular_Gamma_enclosure_per_second'])
        _require(0<lo<=gamma<=hi,'the same positive reference Gamma family is required')
        legs=[]
        for density in raw['two_full_Gaussian_density_sources']:
            pulse=density['Gaussian_source']
            legs.append({'full_raising_operator_norm_upper_per_second':str(field._price_upper(
                gaussian._norm(gaussian._matrix(pulse['source_raising_operator_per_second']),bits)*hi/gamma,bits)),
                'carrier_angular_frequency_absolute_upper_per_second':str(field._price_upper(
                    abs(Q(pulse['carrier_angular_frequency_per_second']))*hi/gamma,bits)),
                'whole_Gaussian_field_area_upper_seconds':str(4*_root_upper(Q(pulse['sigma_squared_seconds']),bits))})
        self._source=source;self._bits=bits
        self._value={'schema':SCHEMA,'complete_atomic_delay_source':raw,'source_two_arm_bounds':legs,
            'translation_law':'integral_R abs(g(t+delta)-g(t)) <= 2 abs(delta)',
            'carrier_law':'abs(exp(-i omega delta)-1) <= min(2, abs(omega delta))',
            'static_H_and_complete_natural_bath_cancel_in_same_Gamma_comparison':True,
            'same_physical_basis_carrier_phase_paid':True,'source_bindings':_bindings(),
            'receipt_measure_or_hardware_membership_supplied':False,'controller_advance':False}
        self._seal=_digest(self._value);_ISSUED[id(self)]=self._seal,source,bits

    def record(self):
        _CHECK();field._closed(self)
        _require(type(self) is RetardedAtomicDelayEnvelope and
            set(vars(self))=={'_source','_bits','_value','_seal'} and
            _ISSUED.get(id(self))==(self._seal,self._source,self._bits) and
            _digest(self._value)==self._seal and self._value['source_bindings']==_bindings() and
            self._source.record()==self._value['complete_atomic_delay_source'],
            'original Gaussian delay family or actual physical-basis variation price changed')
        return _copy(self._value)

    def restriction(self,lower,upper,reference):
        raw=RetardedAtomicDelayEnvelope.record(self)
        lower,upper,reference=map(full.nonnegative,(lower,upper,reference))
        _require(lower<=reference<=upper,'the source anchor belongs to its complete receipt interval')
        lower_flows=self._source.local_intervals(lower)
        upper_flows=self._source.local_intervals(upper);reference_flows=self._source.local_intervals(reference)
        radius=max(reference-lower,upper-reference);terms=[];total=Q(0)
        pulses=raw['complete_atomic_delay_source']['two_full_Gaussian_density_sources']
        for bounds,interval,last,anchor,pulse in zip(raw['source_two_arm_bounds'],lower_flows,upper_flows,reference_flows,pulses):
            flight=interval[1]-interval[0]
            norm=Q(bounds['full_raising_operator_norm_upper_per_second'])
            omega=Q(bounds['carrier_angular_frequency_absolute_upper_per_second'])
            area=Q(bounds['whole_Gaussian_field_area_upper_seconds'])
            maximum=_Gaussian_upper(pulse['Gaussian_source'],interval[0],last[1],self._bits)
            local_area=flight*maximum
            translation=min(local_area,2*radius,2*area)
            phase=min(Q(2),omega*radius)
            translation_price=4*norm*translation
            carrier_price=4*norm*phase*min(local_area,area)
            payment=min(Q(2),translation_price+carrier_price)
            total+=payment
            terms.append({'source_anchor_local_interval_seconds':list(map(str,anchor)),
                'source_flight_seconds':str(flight),'Gaussian_translation_integral_upper_seconds':str(translation),
                'whole_delay_family_Gaussian_envelope_upper':str(maximum),
                'carrier_phase_change_upper':str(phase),'Gaussian_translation_operator_price':str(translation_price),
                'physical_carrier_operator_price':str(carrier_price),
                'complete_local_delay_operator_difference_upper':str(field._price_upper(payment,self._bits))})
        return {'schema':SCHEMA+'/uniform-source-restriction','source_record':raw,
            'physical_receipt_interval_seconds':list(map(str,(lower,upper))),
            'source_anchor_detector_seconds':str(reference),'receipt_radius_seconds':str(radius),
            'two_complete_delay_prices':terms,
            'whole_two_arm_delay_operator_difference_upper':str(field._price_upper(min(Q(2),total),self._bits)),
            'same_lambda_for_all_receipt_times':True,'Duhamel_CPTP_contraction_used':True,
            'Hamiltonian_norm_exponential_used':False,'physical_carrier_phase_variation_paid':True,
            'time_measure_integrated_or_its_error_paid':False}


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _signature():
    helpers=(_require,_copy,_digest,_bindings,_root_upper,_Gaussian_upper,_function,_signature,_check,
        delay.RetardedAtomicDelaySource.record,delay.RetardedAtomicDelaySource.local_intervals,
        gaussian._norm,gaussian._matrix,gaussian._precision,gaussian._exponential,full._sqrt,field._closed,field._price_upper)
    methods=tuple(_function(v) for v in vars(RetardedAtomicDelayEnvelope).values() if callable(v))
    return tuple(map(_function,helpers)),methods,SCHEMA


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature()==_EXPECTED and
        delay._CHECK is _DELAY_CHECK,'source delay envelope execution changed')
    _DELAY_CHECK()


_CHECK,_SIGNATURE=_check,_signature
_EXPECTED=_signature()
