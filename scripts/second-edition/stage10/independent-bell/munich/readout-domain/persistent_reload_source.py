"""Capture, shared APD arrivals and PC polling in one persistent source.

Each event step stops at its first APD arrival or its next deterministic
boundary.  The arrival branch retains the complete event-time quantum
measure.  Its next queue and controller are indexed by that same time;
an integrated poststate never receives an invented arrival timestamp.
"""
from dataclasses import dataclass, replace
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

import atomic_dipole as dipole
import atomic_full_forward as full
import apd_window_history as apd
import fluorescence_channel as channel
import fluorescence_presence as local
import joint_fluorescence_presence as joint
import munich_atomic_programme as atomic
import optical_multitone as optical
import trap_reload_source as trap
import bsm_retry_source as bsm


BASE=Path(__file__).resolve().parent
SCHEMA='stage10-persistent-capture-APD-polling-source/v1'
ZERO=dipole.ComplexRadical()
_ISSUED=set()


def _require(condition,message):
    if not condition:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _code():
    paths=(Path(__file__),Path(atomic.__file__),Path(apd.__file__),Path(trap.__file__),
           Path(joint.__file__),Path(local.__file__),Path(channel.__file__),Path(optical.__file__),Path(full.__file__),Path(dipole.__file__))
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


@dataclass(frozen=True)
class PollRule:
    name: str
    cooling_mask: tuple
    capture_mask: tuple
    threshold: int
    low_next: str
    high_next: str
    low_flags: tuple
    high_flags: tuple
    ready: bool

    def __post_init__(self):
        _require(type(self.name) is str and self.name and type(self.low_next) is str and type(self.high_next) is str,
                 'named raw PC stages and both count successors required')
        for mask in (self.cooling_mask,self.capture_mask):
            _require(type(mask) is tuple and len(mask)==2 and all(type(x) is bool for x in mask),'two raw side control bits required')
        for flags in (self.low_flags,self.high_flags):
            _require(type(flags) is tuple and len(flags)==2 and all(x is None or type(x) is bool for x in flags),
                     'raw PC confirmation updates, with None meaning retained, required')
        _require(type(self.threshold) is int and self.threshold>=1 and type(self.ready) is bool,'raw positive APD threshold and PC ready label required')

    def record(self):
        return {key:list(value) if type(value) is tuple else value for key,value in vars(self).items()}

    @classmethod
    def from_record(cls,record):
        data=dict(record)
        for key in ('cooling_mask','capture_mask','low_flags','high_flags'):
            data[key]=tuple(data[key])
        return cls(**data)


class PersistentState:
    def __init__(self,*args,**kwargs):
        raise ValueError('source-issued persistent state required; a target matrix is not a seed')

    def record(self):
        if _guard is not _GUARD_FUNCTION or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('persistent source execution closure changed')
        _guard()
        if not (type(self) is PersistentState and set(vars(self))=={'_frame','_seal'} and self._seal in _ISSUED
                and _digest(self._frame)==self._seal):
            raise ValueError('persistent source state or callback changed')
        return _copy(self._frame)


def _issue(frame):
    state=object.__new__(PersistentState)
    state._frame=_copy(frame)
    state._seal=_digest(frame)
    _ISSUED.add(state._seal)
    return state


def _read_memory(source,record):
    memory=apd.APDWindowHistorySource.memory(source,record['source_relative_clock'],record['recent_arrival_times'])
    _require(memory.record()==record,'complete APD arrival-memory coimage required')
    return memory


def _restore_state(frame):
    _require(type(frame) is dict,'complete persistent state record required')
    source=PersistentReloadSource.from_record(frame['source_owner'])
    recipe=frame['source_recipe']
    if recipe['kind']=='source-owned basis primitive':
        raw=recipe['raw_seed']
        state=PersistentReloadSource.seed(source,stage=raw['stage'],loaded_flags=tuple(raw['loaded_flags']),
             clock_seconds=raw['clock_seconds'],recent_arrivals_seconds=raw['recent_arrivals_seconds'],
             atomic_primitives=tuple(dipole.State(*entry) for entry in recipe['basis']))
    elif recipe['kind']=='raw field change identity CP action':
        state=PersistentReloadSource.enter_field(source,_restore_state(recipe['incoming_state']),
                  mode=recipe['new_field_mode'],settings=None if recipe['new_field_mode']!='SI' else tuple(frame['field_settings']))
    else:
        original=recipe
        if original['kind']=='APD-count PC successor':
            original=original['parent']
        if original['kind']=='capture-on no-APD branch':
            cell,certificate=original['cell_source'],original['certificate']
            inlet=_restore_state(cell['incoming_state'])
            unit=Q(frame['source_owner']['atomic_owner']['atomic_base']['seconds_per_unit'])
            _,state=PersistentReloadSource.certify_step(source,inlet,certificate['trial_pieces'],
                      duration_seconds=Q(cell['duration'])*unit,**certificate['precision'])
        elif original['kind']=='source first-arrival density next':
            state=PersistentReloadSource.arrival_next_at(source,original['mother_measure'],original['time_coordinate'])
        else:
            raise ValueError('persistent state has no source-generated occurrence provenance')
    _require(PersistentState.record(state)==frame,'persistent quantum state, control or APD genealogy changed')
    return state


def _capture_records(owner,occupations,couplings):
    _require(type(occupations) in (tuple,list) and type(couplings) in (tuple,list) and len(occupations)==len(couplings)==2,
             'both raw reservoir occupation/coupling dictionaries required')
    base=atomic.MunichAtomicProgramme.atomic_base(owner)
    result=[]
    for side in (0,1):
        raw=atomic.AtomicBase.segment(base,side,1)
        bath=local.CounterGenerator(raw,threshold=1,background_rate=0,
               efficiencies={jump.label:0 for jump in local.natural_channels(raw)})
        capture=trap.ReloadSource(bath,reservoir_occupations=occupations[side],capture_couplings=couplings[side])
        result.append(capture.record())
    return result


def _capture_action(matrix,captures,enabled):
    answer={}
    for side,active in enumerate(enabled):
        if not active:
            continue
        for operator in captures[side].birth_operators.values():
            adjoint=dipole.matrix_adjoint(operator)
            loss=dipole.matrix_product(adjoint,operator)
            answer=local._sum(answer,joint._operator_right(joint._operator_left(matrix,side,operator),side,adjoint))
            for term in (joint._operator_left(matrix,side,loss),joint._operator_right(matrix,side,loss)):
                for key,value in term.items():
                    local._add(answer,key,-value*Q(1,2))
    return answer


class _CounterProjection:
    def __init__(self,cell):
        self.record_value=_copy(cell)
        self.apd=apd.APDWindowHistorySource.from_record(cell['APD_source'])
        self.raw=apd.APDWindowHistorySource.first_arrival_source(self.apd)
        self.captures=tuple(trap.ReloadSource.from_record(r) for r in cell['capture_sources'])
        self.dimension,self.threshold,self.duration=joint.DIMENSION,1,self.raw.duration

    def record(self):
        return _copy(self.record_value)

    def action(self,matrix):
        answer=self.raw.action(matrix)
        for counter,block in self.raw._blocks(matrix).items():
            for key,value in _capture_action(block,self.captures,self.record_value['capture_enabled']).items():
                local._add(answer,(counter,*key),value)
        return answer


class SourceKernel(channel.SourceKernel):
    def __init__(self,cell,coefficient_bits=160):
        _require(type(coefficient_bits) is int and 64<=coefficient_bits<=512,'registered coefficient precision required')
        owner=PersistentReloadSource.from_record(cell['persistent_owner'])
        expected=PersistentReloadSource._cell(owner,cell['incoming_state'],cell['duration'])
        _require(expected==cell,'closed persistent capture/APD source cell required; arbitrary G is not input')
        self.source=_CounterProjection(cell)
        self.dimension,self.threshold,self.bits=joint.DIMENSION,1,coefficient_bits
        self.columns,self.exact_columns,self.errors={},{},{}


def _curve(cell,initial,pieces,old_error,precision):
    _require(type(precision['mode_bits']) is int and 32<=precision['mode_bits']<=256 and
             type(precision['exponential_bits']) is int and 64<=precision['exponential_bits']<=1024,
             'registered dyadic mode/scalar precision required')
    kernel=SourceKernel(cell,precision['coefficient_bits'])
    initial=channel._initial(initial,joint.DIMENSION)
    quantum=1<<precision['mode_bits']
    centre,rounding={},Q(0)
    for (i,j),value in initial.items():
        a,da=full.radical_midpoint(value.real,precision['coefficient_bits'])
        b,db=full.radical_midpoint(value.imag,precision['coefficient_bits'])
        channel._add(centre,(0,i,j),a,b)
        rounding+=da+db
    norm=bsm._entry_norm(initial,bits=precision['coefficient_bits'])
    model=Q(cell['source_model_delta'])*norm
    error=full.nonnegative(old_error)+model+rounding
    elapsed,records=Q(0),[]
    _require(type(pieces) is list,'untrusted complete source-time curve pieces required')
    for piece in pieces:
        width,begin,end,prices,diagnostics=channel._piece(kernel,piece,precision['mode_bits'],precision['exponential_bits'])
        gap=channel._difference(begin,centre)
        error+=gap+sum(prices.values(),Q(0))
        elapsed+=width
        _require(elapsed<=kernel.source.duration,'capture/APD curve exceeds its source cell')
        records.append({'duration':str(width),'initial_join_error':str(gap),
                        **{key:str(value) for key,value in prices.items()},'modes':diagnostics})
        centre=end
    _require(elapsed==kernel.source.duration,'capture/APD curve must cover the exact whole source cell')
    pending={(i,j):dipole.ComplexRadical(a,b) for (c,i,j),(a,b) in centre.items() if c==0}
    return {'initial_state':channel._input_record(initial),'trial_pieces':_copy(pieces),'precision':precision,
            'piece_error_records':records,'initial_radical_error':str(rounding),
            'before_model_error':str(old_error),'complete_centre_trace_norm_upper':str(norm),'source_model_payment':str(model),
            'upstream_after_model':str(full.nonnegative(old_error)+model),'global_terminal_error':str(error),
            'no_arrival_poststate':channel._input_record(pending),
            'complete_counter_poststate':[[c,i,j,str(a),str(b)] for (c,i,j),(a,b) in sorted(centre.items())],
            'source_columns_checked':len(kernel.columns),'absent_coordinates_priced':True,'input_positive_certified_here':False}


class PersistentReloadSource:
    def __init__(self,owner,*,reservoir_occupations,capture_couplings,drives,rules,
                 background_rate,collection,poll_period_seconds,poll_phase_seconds,field_phase_origin_seconds,
                 maximum_cell_seconds,phase_policy,arrival_poll_order,compilation_bits=160):
        _require(type(owner) is atomic.MunichAtomicProgramme,'one closed common atomic owner required')
        record=atomic.MunichAtomicProgramme.record(owner)
        _require(type(drives) in (tuple,list) and len(drives)==2 and
                 all(type(side) in (tuple,list) and all(type(d) is atomic.Drive for d in side) for side in drives),
                 'both source-owned cooling/repump drive inventories required')
        _require(type(rules) in (tuple,list) and rules and all(type(rule) is PollRule for rule in rules) and
                 len({r.name for r in rules})==len(rules),'distinct raw PC polling rules required')
        names={r.name for r in rules}
        _require(all(r.low_next in names and r.high_next in names for r in rules),'raw PC successors must stay in the same control carrier')
        _require(phase_policy in ('continuous','restart_on_stage_change') and arrival_poll_order in ('arrival_then_poll','poll_then_arrival'),
                 'explicit optical phase and simultaneous arrival/poll ordering policies required')
        period,maximum=full.exact(poll_period_seconds),full.exact(maximum_cell_seconds)
        phase,origin=full.nonnegative(poll_phase_seconds),full.nonnegative(field_phase_origin_seconds)
        _require(period>0 and maximum>0,'positive raw polling period and field-cell size required')
        maximum_threshold=max(r.threshold for r in rules)
        first,second=(atomic.MunichAtomicProgramme.phase(owner,'native',side,Q(1,25),drives[side]) for side in (0,1))
        raw,_=atomic.MunichAtomicProgramme.native_cell(owner,first,second,(0,first.programme().base.duration),0,
                    threshold=1,background_rate=background_rate,collection=collection,bits=compilation_bits)
        shared=apd.APDWindowHistorySource(raw,seconds_per_unit=record['atomic_base']['seconds_per_unit'],maximum_threshold=maximum_threshold)
        self._frame={'schema':SCHEMA,'atomic_owner':record,'capture_sources':_capture_records(owner,reservoir_occupations,capture_couplings),
             'drives':[[atomic.Drive.record(d) for d in side] for side in drives],
             'rules':[PollRule.record(rule) for rule in rules],'shared_APD':apd.APDWindowHistorySource.record(shared),
             'poll_period_seconds':str(period),'poll_phase_seconds':str(phase),'field_phase_origin_seconds':str(origin),
             'maximum_cell_seconds':str(maximum),'phase_policy':phase_policy,'arrival_poll_order':arrival_poll_order,
             'compilation_bits':compilation_bits,'control_reads_only':'shared APD rolling count; never hidden occupancy',
             'persistent_memory':'full33 pair + arrival queue + PC stage/flags + optical phase clock + source recipe',
             'public_integration_seconds':'1/25','stage_reset_at_CEM':False,'queue_reset_at_CEM':False,
             'actual_initial_state_or_PC_policy_identified':False,'controller_advance':False,'source_code':_code()}
        self._seal=_digest(self._frame)

    def record(self):
        if _guard is not _GUARD_FUNCTION or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('persistent source execution closure changed')
        _guard()
        _require(type(self) is PersistentReloadSource and set(vars(self))=={'_frame','_seal'} and
                 _digest(self._frame)==self._seal and self._frame['source_code']==_code(),'persistent source snapshot/callback changed')
        return _copy(self._frame)

    @classmethod
    def from_record(cls,record):
        _guard()
        _require(cls is PersistentReloadSource and type(record) is dict and record.get('schema')==SCHEMA,'closed persistent source record required')
        owner=atomic.MunichAtomicProgramme.from_record(record['atomic_owner'])
        captures=[trap.ReloadSource.from_record(r) for r in record['capture_sources']]
        raw=joint.JointCounterGenerator.from_record(record['shared_APD']['original_shared_source'])
        collection={tuple(r['label']):tuple(tuple(channel._complex_record(v) for v in row) for row in r['matrix'])
                    for r in raw.record()['collection']}
        result=cls(owner,reservoir_occupations=tuple(c.occupations for c in captures),capture_couplings=tuple(c.couplings for c in captures),
            drives=tuple(tuple(atomic.Drive.from_record(d) for d in side) for side in record['drives']),
            rules=tuple(PollRule.from_record(r) for r in record['rules']),background_rate=raw.background_rate,collection=collection,
            poll_period_seconds=record['poll_period_seconds'],poll_phase_seconds=record['poll_phase_seconds'],
            field_phase_origin_seconds=record['field_phase_origin_seconds'],maximum_cell_seconds=record['maximum_cell_seconds'],
            phase_policy=record['phase_policy'],arrival_poll_order=record['arrival_poll_order'],compilation_bits=record['compilation_bits'])
        _require(result.record()==record,'persistent source/control/unit identity changed')
        return result

    def _apd(self):
        return apd.APDWindowHistorySource.from_record(PersistentReloadSource.record(self)['shared_APD'])

    def _rule(self,name):
        record=PersistentReloadSource.record(self)
        _require(type(name) is str and any(r['name']==name for r in record['rules']),'explicit source PC stage required')
        return next(r for r in record['rules'] if r['name']==name)

    def seed(self,*,stage,loaded_flags,clock_seconds,recent_arrivals_seconds,atomic_primitives):
        record=PersistentReloadSource.record(self)
        rule=PersistentReloadSource._rule(self,stage)
        _require(type(loaded_flags) is tuple and len(loaded_flags)==2 and all(type(v) is bool for v in loaded_flags),
                 'explicit inherited PC loaded flags required; occupancy is not a control input')
        _require(type(atomic_primitives) is tuple and len(atomic_primitives)==2 and all(type(s) is dipole.State and s in dipole.STATES for s in atomic_primitives),
                 'source atomic basis primitives required; an arbitrary density is not input')
        unit=Q(record['atomic_owner']['atomic_base']['seconds_per_unit'])
        memory=apd.APDWindowHistorySource.memory(PersistentReloadSource._apd(self),full.nonnegative(clock_seconds)/unit,
                     tuple(full.nonnegative(t)/unit for t in recent_arrivals_seconds))
        _require(memory.clock*unit>=Q(record['field_phase_origin_seconds']),'source clock precedes the raw optical phase origin')
        index=joint.atom_pair_index(*(dipole.INDEX[s] for s in atomic_primitives))
        frame={'source_owner':record,'quantum_centre':channel._input_record({(index,index):dipole.ComplexRadical(1)}),
               'global_error':'0','memory':memory.record(),'stage':stage,'loaded_flags':list(loaded_flags),
               'field_mode':'native','field_settings':None,'field_started_at':str(memory.clock),
               'phase_started_at':str(Q(record['field_phase_origin_seconds'])/unit),
               'source_recipe':{'kind':'source-owned basis primitive','basis':[[s.family,s.f,s.m] for s in atomic_primitives],
                                'raw_seed':{'stage':stage,'loaded_flags':list(loaded_flags),'clock_seconds':str(clock_seconds),
                                            'recent_arrivals_seconds':list(map(str,recent_arrivals_seconds))},
                                'actual_initial_history_identified':False},'literal_cohort_reconstructed':False}
        return _issue(frame)

    def _state(self,state):
        _require(type(state) is PersistentState,'source-issued persistent state required')
        frame=PersistentState.record(state)
        _require(frame['source_owner']==PersistentReloadSource.record(self),'persistent state belongs to another hardware/control source')
        _read_memory(PersistentReloadSource._apd(self),frame['memory'])
        PersistentReloadSource._rule(self,frame['stage'])
        channel._initial(channel._read_input(frame['quantum_centre'],joint.DIMENSION),joint.DIMENSION)
        return frame

    def _next_poll(self,clock):
        record=PersistentReloadSource.record(self)
        unit=Q(record['atomic_owner']['atomic_base']['seconds_per_unit'])
        phase,period=Q(record['poll_phase_seconds'])/unit,Q(record['poll_period_seconds'])/unit
        index=(clock-phase)//period+1
        return phase+max(0,index)*period

    def _poll(self,frame):
        shared=PersistentReloadSource._apd(self)
        memory=_read_memory(shared,frame['memory'])
        rule=PersistentReloadSource._rule(self,frame['stage'])
        observed=apd.APDWindowHistorySource.observe(shared,memory,threshold=rule['threshold'])
        high=observed['at_least_threshold']
        target=rule['high_next'] if high else rule['low_next']
        changes=rule['high_flags'] if high else rule['low_flags']
        result=_copy(frame)
        result['loaded_flags']=[old if new is None else new for old,new in zip(frame['loaded_flags'],changes)]
        result['stage']=target
        if target!=frame['stage'] and frame['source_owner']['phase_policy']=='restart_on_stage_change':
            result['phase_started_at']=str(memory.clock)
        result['source_recipe']={'kind':'APD-count PC successor','parent':frame['source_recipe'],'observation':observed,
                                 'quantum_occupancy_read':False}
        return result

    def enter_field(self,state,*,mode,settings=None):
        frame=PersistentReloadSource._state(self,state)
        _require(mode in ('native','dark','SI') and (mode!='SI' or type(settings) is tuple and len(settings)==2
                     and all(type(v) is int and v in (0,1) for v in settings)),'raw field mode and SI settings required')
        result=_copy(frame)
        result['field_mode']=mode
        result['field_settings']=list(settings) if mode=='SI' else None
        result['field_started_at']=frame['memory']['source_relative_clock']
        result['source_recipe']={'kind':'raw field change identity CP action','incoming_state':frame,'parent':frame['source_recipe'],
                 'new_field_mode':mode,'arrival_queue_and_PC_state_retained':True,'CEM_click_not_yet_observed':mode=='SI'}
        return _issue(result)

    def _cell(self,frame,duration):
        record=PersistentReloadSource.record(self)
        _require(type(frame) is dict and frame['source_owner']==record,'same persistent source cell inlet required')
        shared=PersistentReloadSource._apd(self)
        memory=_read_memory(shared,frame['memory'])
        width=full.nonnegative(duration)
        _require(width>0 and memory.clock+width<=PersistentReloadSource._next_poll(self,memory.clock),
                 'cell must end at or before the next raw PC poll')
        owner=atomic.MunichAtomicProgramme.from_record(record['atomic_owner'])
        base=atomic.MunichAtomicProgramme.atomic_base(owner)
        unit=Q(base.record()['seconds_per_unit'])
        rule=PersistentReloadSource._rule(self,frame['stage'])
        offset=memory.clock-Q(frame['phase_started_at'])
        atoms,prices,origins=[],[],[]
        for side in (0,1):
            if frame['field_mode']=='native':
                drives=tuple(atomic.Drive.from_record(r) for r in record['drives'][side])
                if not rule['cooling_mask'][side]:
                    drives=tuple(atomic.Drive(d.role,d.beam,0,d.detuning,d.polarization) for d in drives)
                phase=atomic.MunichAtomicProgramme.phase(owner,'native',side,Q(1,25),drives)
                original=atomic.AtomicPhase.programme(phase)
                continuous=optical.Programme(replace(original.base,duration=offset+width),original.tones)
                cell=continuous.compile_cell(offset,offset+width,bits=record['compilation_bits'])
                atom,optical_price=cell.segment,cell.trace_norm_error
                origin={'native_phase':phase.record(),'absolute_phase_cell':cell.record()}
            elif frame['field_mode']=='dark':
                atom=atomic.AtomicBase.segment(base,side,width)
                optical_price=Q(0)
                origin={'dark_field_duration':str(width)}
            else:
                source,si_model=atomic.MunichAtomicProgramme.si_window_source(owner,tuple(frame['field_settings']))
                elapsed=memory.clock-Q(frame['field_started_at'])
                start=Q(0)
                pulse=None
                for value in source.waveforms[side]:
                    if start<=elapsed<start+value.duration:
                        pulse=value
                        _require(elapsed+width<=start+value.duration,'SI event cell crosses a raw waveform boundary')
                        break
                    start+=value.duration
                _require(pulse is not None,'SI field cell outside its source waveform')
                atom=replace(pulse,duration=width)
                optical_price=(Q(si_model['local_prices'][side]['command_trace_norm_error'])*width/pulse.duration
                               if any(pulse.fields_r.values()) else Q(0))
                origin={'common_SI_source':source.record(),'raw_waveform_elapsed':str(elapsed)}
            zeeman_price=2*width*atomic._operator_upper(atomic.AtomicBase.off_diagonal_zeeman(base,side),record['compilation_bits'])
            atoms.append(atom);prices.append(optical_price+zeeman_price);origins.append(origin)
        oldraw=joint.JointCounterGenerator.from_record(record['shared_APD']['original_shared_source'])
        collection={tuple(r['label']):tuple(tuple(channel._complex_record(v) for v in row) for row in r['matrix']) for r in oldraw.record()['collection']}
        raw=joint.JointCounterGenerator(*atoms,threshold=1,background_rate=oldraw.background_rate,collection=collection)
        detector=apd.APDWindowHistorySource(raw,seconds_per_unit=unit,maximum_threshold=shared.maximum_threshold)
        apd.APDWindowHistorySource.retain_on_phase_change(shared,memory,detector)
        enabled=tuple(rule['capture_mask']) if frame['field_mode']=='native' else (False,False)
        return {'schema':SCHEMA+'/capture-cell','persistent_owner':record,'incoming_state':_copy(frame),
                'duration':str(width),'APD_source':detector.record(),'capture_sources':record['capture_sources'],
                'capture_enabled':list(enabled),'source_model_delta':str(sum(prices,Q(0))),'atomic_origins':origins,
                'detected_jump':'original D_shared + one BG identity channel; capture is unobserved',
                'no_arrival_generator':'original unobserved atomic/APD action + enabled source capture dissipators',
                'physical_dimension':joint.DIMENSION,'controller_advance':False}

    def certify_step(self,state,pieces,*,duration_seconds=None,mode_bits=60,coefficient_bits=160,exponential_bits=160):
        frame=PersistentReloadSource._state(self,state)
        record=PersistentReloadSource.record(self)
        clock=Q(frame['memory']['source_relative_clock'])
        unit=Q(record['atomic_owner']['atomic_base']['seconds_per_unit'])
        width=min(Q(record['maximum_cell_seconds'])/unit,PersistentReloadSource._next_poll(self,clock)-clock)
        if frame['field_mode']=='SI':
            owner=atomic.MunichAtomicProgramme.from_record(record['atomic_owner'])
            source,_=atomic.MunichAtomicProgramme.si_window_source(owner,tuple(frame['field_settings']))
            elapsed=clock-Q(frame['field_started_at'])
            for waveform in source.waveforms:
                boundary=Q(0)
                for pulse in waveform:
                    boundary+=pulse.duration
                    if elapsed<boundary:
                        width=min(width,boundary-elapsed)
                        break
        if duration_seconds is not None:
            proposed=full.nonnegative(duration_seconds)/unit
            _require(0<proposed<=width,'explicit event-cell duration exceeds the next source boundary')
            width=proposed
        cell=PersistentReloadSource._cell(self,frame,width)
        initial=channel._read_input(frame['quantum_centre'],joint.DIMENSION)
        certificate=_curve(cell,initial,pieces,frame['global_error'],dict(mode_bits=mode_bits,coefficient_bits=coefficient_bits,exponential_bits=exponential_bits))
        following=_copy(frame)
        shared=apd.APDWindowHistorySource.from_record(cell['APD_source'])
        memory=_read_memory(shared,frame['memory'])
        memory=apd.APDWindowHistorySource.elapse(shared,memory,width)
        following['memory']=memory.record()
        following['quantum_centre']=certificate['no_arrival_poststate']
        following['global_error']=certificate['global_terminal_error']
        following['source_recipe']={'kind':'capture-on no-APD branch','parent':frame['source_recipe'],'cell_source':cell,'certificate':certificate}
        if memory.clock==PersistentReloadSource._next_poll(self,clock):
            following=PersistentReloadSource._poll(self,following)
        next_state=_issue(following)
        return {'schema':SCHEMA+'/event-step','source_record':record,'incoming_state':frame,'cell_source':cell,
                'capture_APD_certificate':certificate,'no_arrival_next_state':PersistentState.record(next_state),
                'first_arrival_next_recipe':'at each exact source time s, apply J to the same c0 curve, elapse/append the same queue, retain PC stage until its poll',
                'count_queue_reset':False,'stage_reset':False,'source_model_and_old_error_paid_once':True,
                'actual_arrival_archive_reconstructed':False,'controller_advance':False},next_state

    def verify_step(self,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/event-step' and
                 report['source_record']==PersistentReloadSource.record(self),'same persistent event-step source required')
        frame=report['incoming_state']
        state=_restore_state(frame)
        precision=report['capture_APD_certificate']['precision']
        unit=Q(frame['source_owner']['atomic_owner']['atomic_base']['seconds_per_unit'])
        expected,_=PersistentReloadSource.certify_step(self,state,report['capture_APD_certificate']['trial_pieces'],
                  duration_seconds=Q(report['cell_source']['duration'])*unit,**precision)
        _require(expected==report,'persistent capture/APD curve, next, queue or model price changed')
        return True

    def first_arrival_measure(self,step,time_cells=None):
        PersistentReloadSource.verify_step(self,step)
        cell,certificate=step['cell_source'],step['capture_APD_certificate']
        shared=apd.APDWindowHistorySource.from_record(cell['APD_source'])
        start=Q(step['incoming_state']['memory']['source_relative_clock'])
        stop=start+Q(cell['duration'])
        cells=((start,stop),) if time_cells is None else tuple(tuple(map(full.exact,c)) for c in time_cells)
        _require(all(len(c)==2 and start<=c[0]<=c[1]<=stop for c in cells) and
                 all(a[1]<=b[0] for a,b in zip(cells,cells[1:])),'disjoint first-arrival source-time restrictions required')
        kernel=SourceKernel(cell,certificate['precision']['coefficient_bits'])
        bound=sum(max(atom.outgoing) for atom in shared._raw.sources)+shared._raw.background_rate
        price=Q(certificate['initial_radical_error'])
        elapsed,error,result=Q(0),Q(0),{}
        quantum=1<<certificate['precision']['mode_bits']
        for piece,paid in zip(certificate['trial_pieces'],certificate['piece_error_records']):
            width=Q(piece['duration'])
            price+=sum(Q(paid[k]) for k in ('initial_join_error','source_residual_error','radical_coefficient_error','scalar_exponential_error'))
            for left,right in cells:
                a,z=max(Q(0),left-start-elapsed),min(width,right-start-elapsed)
                if a>=z:
                    continue
                error+=bound*(z-a)*price
                for mode in piece['modes']:
                    _require(mode['lambda']==[0,0],'source-owned first-arrival measure requires polynomial residual witnesses')
                    for degree,encoded in enumerate(mode['coefficients']):
                        coefficient=channel._hermitian(channel._coefficient(encoded,quantum,kernel))
                        state={(i,j):dipole.ComplexRadical(a,b) for (c,i,j),(a,b) in coefficient.items() if c==0}
                        weight=width*((z/width)**(degree+1)-(a/width)**(degree+1))/(degree+1)
                        for key,value in apd.APDWindowHistorySource.jump_rate(shared,state).items():
                            local._add(result,key,weight*value)
            elapsed+=width
        inherited=Q(certificate['upstream_after_model']) if any(a<b for a,b in cells) else Q(0)
        return {'schema':SCHEMA+'/first-arrival-time-measure','event_step':step,'time_cells':[[str(a),str(b)] for a,b in cells],
                'complete_event_poststate':channel._input_record(result),'global_error':str(inherited+error),
                'old_and_model_error_once':str(inherited),'local_curve_error':str(error),
                'arrival_time_mother_retained':True,'queue_at_time_recipe':'elapse incoming queue to the same s, append s once',
                'terminal_at_least_one_poststate_used':False,'capture_generator_checked':True,'controller_advance':False}

    def stopped_instrument(self,step,time_cells=None):
        measure=PersistentReloadSource.first_arrival_measure(self,step,time_cells)
        cert=step['capture_APD_certificate']
        old=Q(cert['upstream_after_model'])
        endpoint=Q(cert['global_terminal_error'])-old
        return {'schema':SCHEMA+'/complete-stopped-CP-instrument','event_step':step,
                'no_arrival_next_state':step['no_arrival_next_state'],'first_arrival_time_measure':measure,
                'global_error':str(old+endpoint+Q(measure['local_curve_error'])),
                'whole_inherited_and_model_error_once':str(old),'endpoint_local_error':str(endpoint),
                'whole_trace_preserving_on_full_time_interval':time_cells is None,
                'all_arrival_branches_have_source_native_next':True,'no_time_midpoint_inserted':True,'controller_advance':False}

    def arrival_next_at(self,measure,time):
        step=measure['event_step']
        expected=PersistentReloadSource.first_arrival_measure(self,step,measure['time_cells'])
        _require(expected==measure,'same source-owned first-arrival measure required')
        time=full.exact(time)
        _require(any(Q(a)<=time<=Q(b) and Q(a)<Q(b) for a,b in measure['time_cells']),'arrival coordinate outside its mother time measure')
        certificate=step['capture_APD_certificate'];cell=step['cell_source']
        kernel=SourceKernel(cell,certificate['precision']['coefficient_bits'])
        start=Q(step['incoming_state']['memory']['source_relative_clock'])
        local_time=time-start
        elapsed,centre=Q(0),{}
        quantum=1<<certificate['precision']['mode_bits']
        for piece in certificate['trial_pieces']:
            width=Q(piece['duration'])
            if elapsed<=local_time<=elapsed+width:
                u=(local_time-elapsed)/width
                for mode in piece['modes']:
                    _require(mode['lambda']==[0,0],'arrival density consumes the same polynomial witness')
                    for degree,encoded in enumerate(mode['coefficients']):
                        raw=channel._hermitian(channel._coefficient(encoded,quantum,kernel))
                        for (count,i,j),(a,b) in raw.items():
                            if count==0:
                                local._add(centre,(i,j),dipole.ComplexRadical(a,b)*u**degree)
                break
            elapsed+=width
        shared=apd.APDWindowHistorySource.from_record(cell['APD_source'])
        frame=_copy(step['incoming_state'])
        memory=_read_memory(shared,frame['memory'])
        memory=apd.APDWindowHistorySource.elapse(shared,memory,time-memory.clock)
        at_poll=time==PersistentReloadSource._next_poll(self,Q(frame['memory']['source_relative_clock']))
        frame['memory']=memory.record()
        if at_poll and frame['source_owner']['arrival_poll_order']=='poll_then_arrival':
            frame=PersistentReloadSource._poll(self,frame)
        memory=apd.APDWindowHistorySource.append_arrival(shared,memory)
        frame['memory']=memory.record()
        frame['quantum_centre']=channel._input_record(apd.APDWindowHistorySource.jump_rate(shared,centre))
        bound=sum(max(atom.outgoing) for atom in shared._raw.sources)+shared._raw.background_rate
        frame['global_error']=str(bound*Q(certificate['global_terminal_error']))
        frame['source_recipe']={'kind':'source first-arrival density next','parent':frame['source_recipe'],'mother_measure':measure,'time_coordinate':str(time),
                                'state_is_rate_density_not_normalized_event':True,'literal_arrival_archive_reconstructed':False}
        if at_poll and frame['source_owner']['arrival_poll_order']=='arrival_then_poll':
            frame=PersistentReloadSource._poll(self,frame)
        return _issue(frame)


def _signature():
    functions=(_require,_copy,_digest,_code,_issue,_read_memory,_restore_state,_capture_records,_capture_action,_curve,_signature,_guard,
      PollRule.__init__,PollRule.__post_init__,PollRule.record,PollRule.from_record.__func__,PersistentState.record,
      PersistentReloadSource.__init__,PersistentReloadSource.record,PersistentReloadSource.from_record.__func__,
      PersistentReloadSource._apd,PersistentReloadSource._rule,PersistentReloadSource.seed,PersistentReloadSource._state,
      PersistentReloadSource._next_poll,PersistentReloadSource._poll,PersistentReloadSource.enter_field,PersistentReloadSource._cell,
      PersistentReloadSource.certify_step,PersistentReloadSource.verify_step,PersistentReloadSource.first_arrival_measure,
      PersistentReloadSource.stopped_instrument,PersistentReloadSource.arrival_next_at,SourceKernel.__init__,_CounterProjection.__init__,_CounterProjection.action,
      channel.SourceKernel.column,channel.SourceKernel.action,channel._piece,channel._coefficient,channel._hermitian,
      channel._initial,channel._input_record,channel._read_input,trap.ReloadSource.__init__,trap.ReloadSource.from_record.__func__,
      apd.APDWindowHistorySource.record,apd.APDWindowHistorySource.memory,apd.APDWindowHistorySource.elapse,
      apd.APDWindowHistorySource.append_arrival,apd.APDWindowHistorySource.observe,apd.APDWindowHistorySource.jump_rate,
      apd.APDWindowHistorySource.retain_on_phase_change,atomic.MunichAtomicProgramme.record,atomic.MunichAtomicProgramme.native_cell,
      optical.Programme.compile_cell,joint._operator_left,joint._operator_right,dipole.matrix_product,dipole.matrix_adjoint,bsm._entry_norm)
    return (tuple((id(f),id(f.__code__)) for f in functions),tuple(trap.GROUND),dipole.ION,tuple(dipole.STATES),tuple(dipole.INDEX.items()))


def _guard():
    if not (_signature is _SIGNATURE and _signature.__code__ is _SIGNATURE_CODE and _signature()==_EXPECTED):
        raise ValueError('persistent source execution closure changed')


_SIGNATURE=_signature
_SIGNATURE_CODE=_signature.__code__
_GUARD_FUNCTION=_guard
_GUARD_CODE=_guard.__code__
_EXPECTED=_signature()
