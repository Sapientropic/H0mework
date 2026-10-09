"""The source-owned complete Zeeman action enters the original CEM Mark law.

Only the original SI geometry, birth/registration/BG maps and its common
atomic owner generate the source.  Trial curves are numerical witnesses;
the complete original-G columns independently check every residual.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import fluorescence_channel as channel
import fluorescence_presence as local
import joint_fluorescence_presence as joint
import native_tone_frame as native
import munich_atomic_programme as atomic
import reference_response_window_source as response
import window_cem_source as window


SCHEMA='stage10-source-owned-full-Zeeman-CEM/v1'
PHASE_SCHEMA=SCHEMA+'/phase'
_ISSUED=set()


def _require(condition,message):
    if not condition:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    paths=(Path(__file__),*(Path(m.__file__) for m in
        (dipole,full,channel,local,joint,native,atomic,response,window)))
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _closed(value):
    response._closed(value)


class FullZeemanCEMPhase:
    def __init__(self,parent,index):
        _CHECK()
        _require(type(parent) is FullZeemanCEMSource and type(index) is int,
                 'source-issued full-Z CEM phase required')
        source=FullZeemanCEMSource.record(parent)
        self.parent,self.index=parent,index
        self._source_digest=parent._seal
        geometry=window.WindowCEMSource.from_record(source['raw_window_source'])
        self._original=window.WindowCEMSource.phase(geometry,index)
        self._z=tuple(channel._read_input(h,33) for h in source['source_generated_off_diagonal_Z'])
        self.duration,self.interval_start=self._original.duration,self._original.interval_start

    def record(self):
        _CHECK();_closed(self)
        raw=FullZeemanCEMSource.record(self.parent)
        original=window.WindowCEMPhase.record(self._original)
        item=raw['raw_window_source']['phase_inventory'][self.index]
        _require(self.parent._seal==self._source_digest and self._original.index==self.index and
                 original['raw_source']==raw['raw_window_source'] and
                 self.duration==Q(item['duration'])==self._original.duration and
                 self.interval_start==Q(item['interval_start'])==self._original.interval_start and
                 [channel._input_record(h) for h in self._z]==raw['source_generated_off_diagonal_Z'],
                 'source phase, original geometry, clock or complete-Z action changed')
        return {'schema':PHASE_SCHEMA,'source_record_digest':self._source_digest,
            'phase_index':self.index,'original_window_phase':window.WindowCEMPhase.record(self._original),
            'source_generated_Z':_copy(raw['source_generated_off_diagonal_Z']),
            'full_generator':'original WindowCEM Mark GKSL minus i[Z_A+Z_B,rho]'}

    def action(self,state):
        _CHECK();_closed(self)
        result=window.WindowCEMPhase.action(self._original,state)
        for mark,matrix in window._blocks(state).items():
            for side,z in enumerate(self._z):
                for (i,j),value in native._commute(z,matrix,side).items():
                    local._add(result,(mark,i,j),value)
        return result


class _Projection:
    def __init__(self,phase):
        _require(type(phase) is FullZeemanCEMPhase,'closed full-Z source phase required')
        self.phase=phase
        self.duration,self.threshold=phase.duration,3

    def action(self,matrix):
        raw={(window.index_mark(c),i,j):value for (c,i,j),value in matrix.items()}
        return {(window.mark_index(mark),i,j):value for (mark,i,j),value in FullZeemanCEMPhase.action(self.phase,raw).items()}


class SourceKernel(channel.SourceKernel):
    def __init__(self,phase,coefficient_bits=160):
        _CHECK()
        _require(type(phase) is FullZeemanCEMPhase and type(coefficient_bits) is int and 64<=coefficient_bits<=512,
                 'closed complete-Z phase and registered coefficient precision required')
        # The actual column action is rebuilt from the sealed source, not
        # the caller's mutable compiled generators or phase duration.
        self.source=_Projection(FullZeemanCEMPhase(phase.parent,phase.index))
        self.dimension,self.threshold,self.bits=joint.DIMENSION,3,coefficient_bits
        self.columns,self.exact_columns,self.errors={},{},{}


def _step(phase,initial,pieces,upstream,precision):
    window._precisions(**precision)
    matrix=window._initial_marked(initial);centre,rounding=window._center(matrix,precision['coefficient_bits'])
    error=full.nonnegative(upstream)+rounding;kernel=SourceKernel(phase,precision['coefficient_bits'])
    phase=kernel.source.phase
    elapsed=Q(0);payments=[]
    for piece in pieces:
        width,begin,end,prices,diagnostics=channel._piece(kernel,piece,precision['mode_bits'],precision['exponential_bits'])
        gap=channel._difference(begin,centre);error+=gap+sum(prices.values(),Q(0));elapsed+=width
        _require(elapsed<=phase.duration,'full-Z trial crossed the original waveform or fragment-window edge')
        payments.append({'duration':str(width),'initial_join_error':str(gap),
            **{name:str(value) for name,value in prices.items()},'modes':diagnostics});centre=end
    _require(elapsed==phase.duration,'complete original source phase must be covered')
    report={'schema':SCHEMA+'/step','raw_phase':FullZeemanCEMPhase.record(phase),
        'initial_marked_state':window._marked_record(matrix),'upstream_trace_norm_error':str(upstream),
        'initial_radical_error':str(rounding),'trial_pieces':_copy(pieces),'precision':_copy(precision),
        'marked_poststate_center':[[c,i,j,str(a),str(b)] for (c,i,j),(a,b) in sorted(centre.items())],
        'trace_norm_error_bound':str(error),'source_columns_checked':len(kernel.columns),
        'piece_error_records':payments,'full_Z_in_original_residual':True,'source_Z_omission_price':'0',
        'old_error_counted_once':True,'input_positivity_certified_here':False,'source_bindings':_bindings()}
    return centre,error,report


class FullZeemanCEMSource:
    def __init__(self,control):
        _CHECK()
        _require(type(control) is response.ReferenceResponseWindowSource,'closed reference response source required; G or target rho is not input')
        _closed(control)
        raw=response.ReferenceResponseWindowSource.record(control)
        geometry=response.ReferenceResponseWindowSource.window_source(control)
        owner=atomic.MunichAtomicProgramme.from_record(raw['working_atomic_owner'])
        base=atomic.MunichAtomicProgramme.atomic_base(owner)
        z=tuple(atomic.AtomicBase.off_diagonal_zeeman(base,side) for side in (0,1))
        for side,waveform in enumerate(geometry.waveforms):
            for segment in waveform:
                quiet=atomic.AtomicBase.segment(base,side,segment.duration)
                _require(segment.detunings==quiet.detunings and segment.gammas==quiet.gammas and
                         segment.radiation_regime==quiet.radiation_regime,
                         'complete-Z source and original CEM need one common static spectrum and natural bath')
        model=raw['source_model_certificate'];price=Q(model['reference_Gamma_static_and_natural_price'])+Q(model['reference_command_trace_norm_error'])
        self._control,self._geometry,self._z=control,geometry,z
        self._value={'schema':SCHEMA,'reference_response_source':raw,'raw_window_source':geometry.record(),
            'working_atomic_owner':raw['working_atomic_owner'],'reference_clock':raw['reference_clock'],
            'source_generated_off_diagonal_Z':[channel._input_record(h) for h in z],
            'source_model_trace_norm_error':str(price),
            'remaining_source_model_certificate':{'reference_Gamma_static_and_natural_price':model['reference_Gamma_static_and_natural_price'],
                'reference_command_trace_norm_error':model['reference_command_trace_norm_error'],
                'source_Z_omission_price':'0','original_priced_compilation_record_preserved':True},
            'source_CPTP_law':'original positive marked CEM GKSL plus a source-generated Hermitian Hamiltonian commutator',
            'fragment_birth_and_mark_logic_changed':False,'BG_applied_once_at_original_cutoff':True,
            'free_generator_or_target_poststate_input':False,'source_bindings':_bindings(),'controller_advance':False}
        self._seal=_digest(self._value);_ISSUED.add(self._seal)

    def record(self):
        _CHECK();_closed(self)
        _require(type(self) is FullZeemanCEMSource and set(vars(self))=={'_control','_geometry','_z','_value','_seal'} and
            self._seal in _ISSUED and _digest(self._value)==self._seal and self._value['source_bindings']==_bindings() and
            response.ReferenceResponseWindowSource.record(self._control)==self._value['reference_response_source'] and
            window.WindowCEMSource.record(self._geometry)==self._value['raw_window_source'] and
            [channel._input_record(h) for h in self._z]==self._value['source_generated_off_diagonal_Z'],
            'full-Z source, geometry, original physical control or remaining model price changed')
        return _copy(self._value)

    @classmethod
    def from_record(cls,record):
        _require(cls is FullZeemanCEMSource and type(record) is dict and record.get('schema')==SCHEMA,
                 'closed full-Z CEM source record required')
        result=cls(response.ReferenceResponseWindowSource.from_record(record['reference_response_source']))
        _require(result.record()==record,'complete-Z source identity changed')
        return result

    def geometry_source(self):
        raw=FullZeemanCEMSource.record(self)
        return window.WindowCEMSource.from_record(raw['raw_window_source'])

    def phases(self):
        FullZeemanCEMSource.record(self)
        return tuple(FullZeemanCEMPhase(self,index) for index in range(len(self._geometry.partition)))

    def generate_trials(self,initial,*,order=8,mode_bits=60,coefficient_bits=160,exponential_bits=160):
        _require(type(order) is int and 0<=order<=64,'untrusted source polynomial order required')
        window._precisions(mode_bits,coefficient_bits,exponential_bits)
        matrix=channel._initial(initial,joint.DIMENSION)
        centre,_=window._center({(0,i,j):v for (i,j),v in matrix.items()},coefficient_bits)
        families=[];quantum=1<<mode_bits
        for phase in FullZeemanCEMSource.phases(self):
            kernel=SourceKernel(phase,coefficient_bits);current=centre;coefficients=[];endpoint={}
            for degree in range(order+1):
                dyadic={key:(Q(round(a*quantum),quantum),Q(round(b*quantum),quantum))
                        for key,(a,b) in current.items() if round(a*quantum) or round(b*quantum)}
                coefficients.append([[c,i,j,int(a*quantum),int(b*quantum)] for (c,i,j),(a,b) in sorted(dyadic.items())])
                for key,(a,b) in dyadic.items():
                    full._add(endpoint,key,a,b)
                current={key:(a*phase.duration/(degree+1),b*phase.duration/(degree+1))
                         for key,(a,b) in kernel.action(dyadic).items()}
            families.append([{'duration':str(phase.duration),'modes':[{'lambda':[0,0],'coefficients':coefficients}]}])
            centre=channel._hermitian(endpoint)
        return families

    def image(self,initial,families,precision):
        record=FullZeemanCEMSource.record(self)
        _require(type(precision) is dict and set(precision)=={'mode_bits','coefficient_bits','exponential_bits'},
                 'complete original checker precision required')
        phases=FullZeemanCEMSource.phases(self)
        _require(type(families) is list and len(families)==len(phases),'every original waveform and fragment-window phase needs a source trial')
        matrix=channel._initial(initial,joint.DIMENSION)
        marked={(window.INITIAL,i,j):v for (i,j),v in matrix.items()};error=Q(0);reports=[]
        for phase,pieces in zip(phases,families):
            centre,error,report=_step(phase,marked,pieces,error,precision)
            reports.append(report);marked={(window.index_mark(c),i,j):dipole.ComplexRadical(a,b) for (c,i,j),(a,b) in centre.items()}
        final=window.WindowCEMSource.background_action(self._geometry,marked)
        outputs=tuple({(i,j):v for (mark,i,j),v in final.items() if mark==selected} for selected in window.MARKS)
        _require(record==FullZeemanCEMSource.record(self),'CEM source changed during original-G checking')
        return outputs,error,reports


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _signature():
    helpers=(_require,_copy,_digest,_bindings,_closed,_step,_function,_signature,_check,
        response._CHECK,response.ReferenceResponseWindowSource.record,response.ReferenceResponseWindowSource.window_source,
        window.WindowCEMSource.phase,window.WindowCEMSource.record,window.WindowCEMSource.from_record,
        window.WindowCEMSource.background_action,window.WindowCEMPhase.action,window.WindowCEMPhase.record,
        window._blocks,window._initial_marked,window._center,window._marked_record,window._precisions,
        window.index_mark,window.mark_index,
        channel.SourceKernel.column,channel.SourceKernel.action,channel.SourceKernel.coefficient_error,
        channel._piece,channel._difference,channel._initial,channel._hermitian,channel._input_record,channel._read_input,
        native._commute,joint._operator_left,joint._operator_right,local._add,
        atomic.MunichAtomicProgramme.from_record,atomic.MunichAtomicProgramme.atomic_base,
        atomic.AtomicBase.segment,atomic.AtomicBase.off_diagonal_zeeman,full.radical_midpoint)
    methods=tuple(_function(v) for cls in (FullZeemanCEMSource,FullZeemanCEMPhase,_Projection,SourceKernel)
        for v in vars(cls).values() if callable(v) or isinstance(v,(classmethod,staticmethod)))
    return tuple(map(_function,helpers)),methods,tuple(dipole.STATES),tuple(window.MARKS),SCHEMA


def _check():
    if _check is not _CHECK or _check.__code__ is not _CHECK_CODE or _signature is not _SIGNATURE or \
       _signature.__code__ is not _SIGNATURE_CODE or _signature()!=_EXPECTED:
        raise ValueError('full-Z CEM executed source closure changed')
    response._CHECK()


_SIGNATURE,_SIGNATURE_CODE=_signature,_signature.__code__
_CHECK,_CHECK_CODE=_check,_check.__code__
_EXPECTED=_signature()
