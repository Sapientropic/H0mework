"""The source-invariant two-empty-atom face has an exact joint receipt law.

All four original BG patterns are integrated from the original gate origin.
This is a projected CP face of the complete field mother; it does not replace
other occupation sectors or erase their coherence and subsequent history.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import retarded_gaussian_bsm_source as retarded
import prepared_retarded_gaussian_inlet as prepared

field, gaussian, dipole, full, channel, joint, bsm = (retarded.field,retarded.gaussian,retarded.dipole,
    retarded.full,retarded.channel,retarded.joint,retarded.bsm)
SCHEMA = 'stage10-source-retarded-two-empty-receipt-time-face/v1'
_ISSUED = {}
_RETARDED_CHECK,_PREPARED_CHECK = retarded._CHECK,prepared._CHECK


def _require(value,message):
    if not value:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in
        (Path(__file__),*(Path(m.__file__) for m in (retarded,prepared,gaussian,field,dipole,full,channel,joint,bsm)))}


def _empty_face(raw):
    for leg in raw['complete_driven_field_source']['Gaussian_source_legs']:
        for name in ('complete_static_H_per_second','source_raising_operator_per_second'):
            matrix = gaussian._matrix(leg[name])
            _require(not any((i==dipole.ION)!=(j==dipole.ION) for i,j in matrix),
                     'the same source Hamiltonian must preserve actual ionic occupation')
        r = gaussian._matrix(leg['complete_natural_R_per_second'])
        _require(not any(i==dipole.ION or j==dipole.ION for i,j in r), 'the empty atom has no source natural loss')
        for item in leg['original_physical_natural_jumps']:
            matrix = gaussian._matrix(item['normalized_natural_jump_operator'])
            _require(not any(i==dipole.ION or j==dipole.ION for i,j in matrix),
                     'all original radiating columns vanish on the empty source sector')
    return joint.atom_pair_index(dipole.ION,dipole.ION)


class RetardedEmptyReceiptTimeMeasure:
    def __init__(self,law):
        _CHECK();field._closed(law)
        _require(type(law) is retarded.RetardedGaussianBSMSource,'closed original retarded law required; empty effects are generated')
        raw = retarded.RetardedGaussianBSMSource.record(law)
        _require(law._groups==retarded._closed_groups(raw['complete_driven_field_source']), 'executed source natural groups changed')
        self._law=law;self._empty=_empty_face(raw)
        common=retarded.optical.CommonOpticalReadout.from_record(raw['complete_driven_field_source']['working_common_optical_source'])
        self._background=retarded.original.PortBackgroundLaw(common)
        bg=retarded.original.PortBackgroundLaw.record(self._background)
        _require(bg==raw['BG_source'],'the empty face uses the very same original four BG and mark source')
        self._value={'schema':SCHEMA,'complete_retarded_field_mother':raw,'BG_source':bg,
            'generated_empty_pair_coordinate':self._empty,'source_bindings':_bindings(),
            'all_signal_operators_vanish_on_this_source_face':True,'whole_field_mother_replaced_by_empty_face':False,
            'complete_other_occupation_and_field_coherence_discarded':False,'controller_advance':False}
        self._seal=_digest(self._value);_ISSUED[id(self)]=self._seal,self._empty

    def record(self):
        _CHECK();field._closed(self);owned=_ISSUED.get(id(self))
        _require(type(self) is RetardedEmptyReceiptTimeMeasure and
            set(vars(self))=={'_law','_empty','_background','_value','_seal'} and owned==(self._seal,self._empty) and
            _digest(self._value)==self._seal and self._value['source_bindings']==_bindings() and
            retarded.RetardedGaussianBSMSource.record(self._law)==self._value['complete_retarded_field_mother'] and
            retarded.original.PortBackgroundLaw.record(self._background)==self._value['BG_source'],
            'source empty face, original gate or actual background law changed')
        _require(self._law._groups==retarded._closed_groups(self._value['complete_retarded_field_mother']['complete_driven_field_source']),
                 'executed source natural groups changed')
        return _copy(self._value)

    def interval(self,start,stop,*,bits=192):
        raw=RetardedEmptyReceiptTimeMeasure.record(self);gaussian._precision(bits)
        start,stop=map(full.nonnegative,(start,stop));g0,g1=map(Q,raw['complete_retarded_field_mother']['gate_seconds'])
        _require(g0<=start<=stop<=g1,'empty receipt time restriction must retain the original detector gate')
        report=retarded.original.PortBackgroundLaw.interval(self._background,start-g0,stop-g0,duration=g1-g0,bits=bits)
        source=raw['complete_retarded_field_mother']['complete_driven_field_source']
        clock=source['Gaussian_source_legs'][0]['reference_clock']
        _require(all(leg['reference_clock']==clock for leg in source['Gaussian_source_legs']), 'one true reference Gamma family required')
        gamma=Q(clock['Gamma_numerical_centre']);lo,hi=map(Q,clock['angular_Gamma_enclosure_per_second'])
        delta=max(abs(gamma-lo),abs(hi-gamma));beta=sum(map(Q,raw['BG_source']['BG_rates_per_second']),Q(0))
        model=Q(0) if start==stop else 2*delta/gamma*beta*(stop-g0)
        patterns=[]
        for item in report['four_first_receipt_masses']:
            centre=Q(item['centre']) if start<stop else Q(0)
            scalar=Q(item['error']) if start<stop else Q(0);error=scalar+model
            patterns.append({'pattern':item['pattern'], 'empty_pair_poststate':channel._input_record({(self._empty,self._empty):dipole.ComplexRadical(centre)}),
                'centre_mass':str(centre),'scalar_BG_integration_price':str(field._price_upper(scalar,bits)),
                'Gamma_BG_history_price':str(field._price_upper(model,bits)),
                'whole_trace_norm_error':str(field._price_upper(error,bits)),
                'true_empty_effect_upper':str(field._price_upper(min(Q(1),max(Q(0),centre+error)),bits))})
        return {'schema':SCHEMA+'/integrated-projected-CP-face','source_record':raw,
            'original_BG_time_certificate':report,'physical_first_receipt_interval_seconds':list(map(str,(start,stop))),
            'four_pattern_poststates':patterns,'scalar_bits':bits,
            'exact_zero_from_empty_time_interval':start==stop,
            'empty_signal_vacuum_used_only_on_invariant_empty_face':True,'whole_field_or_actual_hardware_identity_asserted':False}

    def apply_inlet(self,inlet,start,stop,*,bits=192):
        _CHECK();field._closed(inlet)
        _require(type(inlet) is prepared.PreparedRetardedGaussianInlet and inlet._law is self._law,
                 'same source-issued retarded inlet required; empty population is not input')
        source=prepared.PreparedRetardedGaussianInlet.source_tensors(inlet)
        mass=dipole.ComplexRadical()
        for a,b in source['tensor_terms']:
            mass += a.get((dipole.ION,dipole.ION),dipole.ComplexRadical())*b.get((dipole.ION,dipole.ION),dipole.ComplexRadical())
        _require(not mass.imag,'the generated source empty population is real')
        centre,rounding=full.radical_midpoint(mass.real,bits)
        old=Q(source['whole_upstream_trace_norm_error']);report=RetardedEmptyReceiptTimeMeasure.interval(self,start,stop,bits=bits)
        patterns=[]
        for item in report['four_pattern_poststates']:
            p=Q(item['centre_mass']);ep=Q(item['whole_trace_norm_error']);cap=Q(item['true_empty_effect_upper'])
            payment=cap*(old+rounding)+abs(centre)*ep
            output=centre*p
            patterns.append({'pattern':item['pattern'],'empty_pair_poststate':channel._input_record({(self._empty,self._empty):dipole.ComplexRadical(output)}),
                'centre_mass':str(output),'whole_inlet_error_payment_once':str(field._price_upper(cap*old,bits)),
                'new_BG_and_population_scalar_price':str(field._price_upper(payment-cap*old,bits)),
                'whole_trace_norm_error':str(field._price_upper(payment,bits)),
                'projected_receipt_mass_lower':str(max(Q(0),output-payment))})
        union_cap=min(Q(1),sum((Q(item['true_empty_effect_upper']) for item in report['four_pattern_poststates']),Q(0)))
        union_centre=centre*sum((Q(item['centre_mass']) for item in report['four_pattern_poststates']),Q(0))
        union_new=union_cap*rounding+abs(centre)*sum((Q(item['whole_trace_norm_error']) for item in report['four_pattern_poststates']),Q(0))
        union_error=union_cap*old+union_new
        return {'schema':SCHEMA+'/source-issued-projected-receipt','source_inlet':source['source_record'],
            'empty_source_population_centre':str(centre),'source_empty_population_error':str(field._price_upper(old+rounding,bits)),
            'original_empty_time_face':report,'four_pattern_poststates':patterns,
            'whole_receipt_union':{'centre_mass':str(union_centre),'true_empty_union_effect_upper':str(union_cap),
                'whole_inlet_error_payment_once':str(field._price_upper(union_cap*old,bits)),
                'new_BG_and_population_scalar_price':str(field._price_upper(union_new,bits)),
                'whole_trace_norm_error':str(field._price_upper(union_error,bits)),
                'projected_receipt_mass_lower':str(max(Q(0),union_centre-union_error))},
            'retained_time_state_mother':source['retained_time_state_mother'],
            'physical_clock_source_joint_square_certified':False,'full_record_domain_or_hardware_identity_asserted':False}


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _signature():
    helpers=(_require,_copy,_digest,_bindings,_empty_face,_function,_signature,_check,
        retarded.RetardedGaussianBSMSource.record,retarded._closed_groups,
        retarded.original.PortBackgroundLaw.record,retarded.original.PortBackgroundLaw.interval,
        retarded.optical.CommonOpticalReadout.from_record,
        prepared.PreparedRetardedGaussianInlet.source_tensors,gaussian._matrix,full.radical_midpoint,
        field._closed,field._price_upper,channel._input_record)
    methods=tuple(_function(v) for v in vars(RetardedEmptyReceiptTimeMeasure).values() if callable(v))
    return tuple(map(_function,helpers)),methods,SCHEMA,dipole.ION


def _check():
    _require(_check is _CHECK and _signature is _SIGNATURE and _signature()==_EXPECTED and
        retarded._CHECK is _RETARDED_CHECK and prepared._CHECK is _PREPARED_CHECK,
        'source empty receipt time instrument execution changed')
    _RETARDED_CHECK();_PREPARED_CHECK()


_CHECK,_SIGNATURE=_check,_signature
_EXPECTED=_signature()
