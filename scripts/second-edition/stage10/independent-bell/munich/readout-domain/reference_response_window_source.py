"""The paid SI primitives generate one reference-clock response waveform.

Physical SI controls and edges are fixed by their original clock chart.
The natural bath and complete Zeeman source belong to the reference owner;
the original WindowCEM checker consumes its diagonal compilation and price.
"""
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import fluorescence_channel as channel
import munich_atomic_programme as atomic
import reference_local_phase_source as reference
import receipt_triggered_programme as response
import registration_joint_transport as transport
import window_cem_source as window


SCHEMA='stage10-reference-clock-paid-physical-SI-response/v1'
_ISSUED=set()


def _require(condition,message):
    if not condition:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    modules=(dipole,full,channel,atomic,reference,response,transport,window)
    paths=(Path(__file__),*(Path(m.__file__) for m in modules))
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _closed(value):
    for cls in type(value).__mro__:
        for name,member in vars(cls).items():
            if callable(member) or isinstance(member,(classmethod,staticmethod,property)):
                _require(name not in vars(value),'source operations cannot be instance callbacks')


def _generate(parent,timing,settings,registration_coordinates):
    raw=reference.ReferenceLocalPhaseSource.record(parent)
    owner=atomic.MunichAtomicProgramme.from_record(raw['working_atomic_owner'])
    base=atomic.MunichAtomicProgramme.atomic_base(owner)
    unit=Q(base.record()['seconds_per_unit']);clock=raw['reference_clock']
    gamma=Q(clock['Gamma_numerical_centre']);ghi=max(gamma,Q(clock['angular_Gamma_enclosure_per_second'][1]))
    delta=Q(clock['Gamma_numerical_error'])
    _require(unit==1/gamma and timing.seconds_per_unit==unit,'response and photon source need the same reference clock')
    original=raw['reference_native_source_record']['common_normalized_atomic_owner']
    leaf=original['paid_si_leaf']
    _require(type(leaf) is dict,'the original normalized owner must retain its frozen paid SI primitives')
    original_owner=atomic.MunichAtomicProgramme.from_record(original)
    _require(atomic.MunichAtomicProgramme.record(original_owner)['paid_si_leaf']==leaf and
             atomic.MunichAtomicProgramme.record(owner)['paid_si_leaf'] is None,
             'the new-unit working owner must not be relabelled as an old paid SI leaf')
    template=full.Segment.from_record(leaf['raw_template'])
    old=transport.source_for_settings(leaf['run'],template,settings,geometry=leaf['geometry'],
        registration_coordinates=registration_coordinates)
    programs=transport._side_programs(leaf['run'],template)
    old_unit=old.seconds_per_unit;time_scale=old_unit/unit;rate_scale=unit/old_unit
    events=timing.events();terminal=max(event['CEM_logic_deadline'] for event in events)
    waveforms=[];registrations=[];local_prices=[];physical_controls=[]
    total_zeeman=Q(0);total_gamma=Q(0);total_command=Q(0)
    for side,(waveform,registration,event) in enumerate(zip(old.waveforms,old.registrations,events)):
        onset=event['readout_reaches_atom'];rows=[base.segment(side,onset)];elapsed=onset
        controls=[]
        for pulse in waveform:
            if elapsed>=event['CEM_logic_deadline']:
                break
            width=min(pulse.duration*time_scale,event['CEM_logic_deadline']-elapsed)
            ion={state:rate*rate_scale for state,rate in pulse.ion_rates.items()}
            compiled=base.segment(side,width,ion_rates=ion,r=pulse.r*rate_scale,c=pulse.c*rate_scale)
            compiled=replace(compiled,fields_r=pulse.fields_r,fields_c=pulse.fields_c)
            _require(width*unit<=pulse.duration*old_unit and compiled.r*(1/unit)==pulse.r*(1/old_unit) and
                     compiled.c*(1/unit)==pulse.c*(1/old_unit) and all(compiled.ion_rates[s]/unit==pulse.ion_rates[s]/old_unit
                                                           for s in full.EXCITED),
                     'physical SI duration, electric coupling or ion rate changed during chart conversion')
            _require(not any(compiled.ion_rates.values()) or elapsed+width<=event['ion_acceptance_window_closes'],
                     'source ion birth outlasts its original acceptance window')
            rows.append(compiled);controls.append({'physical_begin_seconds':str(elapsed*unit),
                'physical_duration_seconds':str(width*unit),'physical_r_per_second':(compiled.r*(1/unit)).serialize(),
                'physical_c_per_second':(compiled.c*(1/unit)).serialize(),
                'physical_ion_rates_per_second':{str(dipole.INDEX[s]):str(compiled.ion_rates[s]/unit) for s in full.EXCITED}})
            elapsed+=width
        _require(elapsed==event['CEM_logic_deadline'],'paid SI primitive waveform must reach its complete local cutoff')
        if elapsed<terminal:
            rows.append(base.segment(side,terminal-elapsed))
        waveforms.append(tuple(rows));physical_controls.append(controls)
        end=event['ion_acceptance_window_closes']
        registrations.append(window.FragmentRegistration(registration.probabilities,
            registration.electron_flight*time_scale,registration.ion_flight*time_scale,
            tuple(onset+t*time_scale for t in registration.electron_window),
            (end-(240 if side==0 else 220)*response.NS/unit,end)))
        static=base.segment(side,1,r=0,c=0)
        h=dipole.hamiltonian(static.fields_r,static.fields_c,static.r,static.c,static.detunings,
            convention=static.field_convention)
        z=base.off_diagonal_zeeman(side)
        hfull=atomic.optical._sum(h,z)
        znorm=atomic._operator_upper(z,192);hnorm=atomic._operator_upper(hfull,192)
        outgoing=max(static.gammas.values())
        duration=terminal*unit
        zeeman=2*ghi*duration*znorm
        gprice=delta*duration*(2*hnorm+2*outgoing)
        old_command=programs[side][settings[side]].command_trace_norm_error
        command=old_command*ghi/gamma
        total_zeeman+=zeeman;total_gamma+=gprice;total_command+=command
        local_prices.append({'side':side,'complete_physical_response_duration_seconds':str(duration),
            'source_full_static_H_norm_upper':str(hnorm),'source_off_diagonal_Z_norm_upper':str(znorm),
            'source_normalized_natural_outgoing_upper':str(outgoing),'full_Zeeman_omission_price':str(zeeman),
            'reference_Gamma_static_and_natural_price':str(gprice),
            'original_command_trace_norm_error':str(old_command),'reference_command_trace_norm_error':str(command),
            'command_price_rule':'physical r/c and pulse width are unchanged; Gamma_hi/Gamma_c is a conservative multiplier',
            'full_off_diagonal_Zeeman':channel._input_record(z)})
    source=window.WindowCEMSource(*waveforms,registrations=tuple(registrations),backgrounds=old.backgrounds,
        logic_deadlines=tuple(event['CEM_logic_deadline'] for event in events),seconds_per_unit=unit)
    model=total_zeeman+total_gamma+total_command
    value={'schema':SCHEMA,'reference_local_parent':raw,'working_atomic_owner':atomic.MunichAtomicProgramme.record(owner),
        'reference_clock':clock,'raw_receipt_timing':response.PublicResponseTiming.record(timing),
        'settings':list(settings),'registration_coordinates':[list(map(str,pair)) for pair in registration_coordinates],
        'original_paid_SI_primitives':leaf,'original_paid_window_source':old.record(),
        'original_seconds_per_source_unit':str(old_unit),'reference_seconds_per_source_unit':str(unit),
        'time_chart_multiplier':str(time_scale),'rate_chart_multiplier':str(rate_scale),
        'physical_SI_waveforms':physical_controls,'raw_window_source':source.record(),
        'original_relative_CEM_cutoffs_seconds':[str(t*old_unit) for t in old.logic_deadlines],
        'receipt_relative_SI_onsets_seconds':[str(event['readout_reaches_atom']*unit) for event in events],
        'source_model_trace_norm_error':str(model),'source_model_certificate':{'local_prices':local_prices,
            'full_Zeeman_omission_price':str(total_zeeman),'reference_Gamma_static_and_natural_price':str(total_gamma),
            'reference_command_trace_norm_error':str(total_command),'induced_trace_norm_error_upper':str(model),
            'complete_input_centre_norm_multiplier_required':True,'old_input_error_repeated_here':False,
            'pulse_edges_fixed_in_physical_seconds':True,'Gamma_dependent_pulse_edge_shift_ignored':False},
        'new_unit_owner_given_old_paid_leaf':False,'reference_natural_bath_and_static_spectrum_used':True,
        'full_Zeeman_source_priced':True,'original_fragment_joint_probabilities_and_BG_preserved':True,
        'new_forward_solve_or_archive_read':False,'actual_hardware_parameters_identified':False,
        'source_bindings':_bindings(),'controller_advance':False}
    return source,value


class ReferenceResponseWindowSource:
    def __init__(self,parent,timing,*,settings,registration_coordinates=((0,0),(0,0))):
        if _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
            raise ValueError('reference SI response executed source closure changed')
        _CHECK()
        _require(type(parent) is reference.ReferenceLocalPhaseSource and type(timing) is response.PublicResponseTiming,
                 'closed reference local parent and source-owned public receipt timing required')
        _closed(parent);_closed(timing)
        _require(type(settings) is tuple and len(settings)==2 and all(type(x) is int and x in (0,1) for x in settings),
                 'two original SI settings required')
        _require(type(registration_coordinates) is tuple and len(registration_coordinates)==2 and
                 all(type(pair) is tuple and len(pair)==2 for pair in registration_coordinates),
                 'two source fragment-registration coordinate pairs required')
        timing_copy=response.PublicResponseTiming.from_record(response.PublicResponseTiming.record(timing))
        source,value=_generate(parent,timing_copy,settings,registration_coordinates)
        self._parent,self._timing,self._source,self._value=parent,timing_copy,source,value
        self._seal=_digest(value);_ISSUED.add(self._seal)

    def record(self):
        if _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
            raise ValueError('reference SI response executed source closure changed')
        _CHECK();_closed(self)
        _require(type(self) is ReferenceResponseWindowSource and
            set(vars(self))=={'_parent','_timing','_source','_value','_seal'} and self._seal in _ISSUED and
            _digest(self._value)==self._seal and self._value['source_bindings']==_bindings() and
            reference.ReferenceLocalPhaseSource.record(self._parent)==self._value['reference_local_parent'] and
            response.PublicResponseTiming.record(self._timing)==self._value['raw_receipt_timing'] and
            window.WindowCEMSource.record(self._source)==self._value['raw_window_source'],
            'reference response source, physical waveform, model price or timing changed')
        return _copy(self._value)

    def window_source(self):
        raw=ReferenceResponseWindowSource.record(self)
        return window.WindowCEMSource.from_record(raw['raw_window_source'])

    @classmethod
    def from_record(cls,record):
        _require(cls is ReferenceResponseWindowSource and type(record) is dict and record.get('schema')==SCHEMA,
                 'closed reference SI response source record required')
        result=cls(reference.ReferenceLocalPhaseSource.from_record(record['reference_local_parent']),
            response.PublicResponseTiming.from_record(record['raw_receipt_timing']),settings=tuple(record['settings']),
            registration_coordinates=tuple(tuple(pair) for pair in record['registration_coordinates']))
        _require(result.record()==record,'original SI primitive, reference clock or source model changed')
        return result


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _signature():
    functions=(_require,_copy,_digest,_bindings,_closed,_generate,_function,_signature,_check,
        reference.ReferenceLocalPhaseSource.record,reference.ReferenceLocalPhaseSource.from_record,
        response.PublicResponseTiming.record,response.PublicResponseTiming.events,response.PublicResponseTiming.from_record,
        atomic.MunichAtomicProgramme.from_record,atomic.MunichAtomicProgramme.record,atomic.MunichAtomicProgramme.atomic_base,
        atomic.AtomicBase.segment,atomic.AtomicBase.off_diagonal_zeeman,atomic._operator_upper,atomic.optical._sum,
        transport.source_for_settings,transport._side_programs,dipole.hamiltonian,
        transport.commands.compile_commands,transport.commands.nominal_command,transport.commands._field,
        transport.commands._hamiltonian_column_bound,transport.commands._sqrt_bounds,
        transport.domain.registration_face,transport.domain.source_registration_point,
        window.WindowCEMSource.__init__,window.WindowCEMSource.record,window.WindowCEMSource.from_record,
        window.FragmentRegistration.__init__,channel._input_record)
    methods=tuple(_function(member) for member in vars(ReferenceResponseWindowSource).values()
                  if callable(member) or isinstance(member,(classmethod,staticmethod)))
    angles=tuple((side,tuple(row)) for side,row in sorted(transport.commands.SIDE_ANGLES.items()))
    return tuple(map(_function,functions)),methods,tuple(dipole.STATES),angles,SCHEMA


def _check():
    if _check is not _CHECK or _check.__code__ is not _CHECK_CODE or _signature is not _SIGNATURE or \
       _signature.__code__ is not _SIGNATURE_CODE or _signature()!=_EXPECTED:
        raise ValueError('reference SI response executed source closure changed')


_SIGNATURE,_SIGNATURE_CODE=_signature,_signature.__code__
_CHECK,_CHECK_CODE=_check,_check.__code__
_EXPECTED=_signature()
