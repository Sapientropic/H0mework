"""Exact native single-carrier frame on the original persistent Ready mother.

The frame transforms the original time-dependent Hamiltonian, resolved bath,
shared APD and unobserved capture together.  Residuals are checked against
the resulting constant source, and the complete pair is returned to the
original physical frame.  No midpoint Hamiltonian or model price is reused.
"""
from dataclasses import replace
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import atomic_modes as modes
import fluorescence_channel as channel
import fluorescence_presence as local
import joint_fluorescence_presence as joint
import munich_atomic_programme as atomic
import optical_multitone as multitone
import persistent_reload_source as persistent
import persistent_ready_mother as ready
import trap_reload_source as trap
import bsm_retry_source as bsm


SCHEMA='stage10-exact-native-single-carrier-frame/v1'
ZERO=dipole.ComplexRadical()
_ISSUED=set()
_REPORTS=set()


def _require(value,message):
    if not value:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    modules=(dipole,full,modes,channel,local,joint,atomic,multitone,persistent,ready,trap,bsm)
    paths=(Path(__file__),*(Path(m.__file__) for m in modules))
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _read(record):
    return {(i,j):channel._complex_record(v) for i,j,v in record}


def _commute(h,m,side):
    answer={}
    for key,value in joint._operator_left(m,side,h).items():
        local._add(answer,key,dipole.ComplexRadical(0,-1)*value)
    for key,value in joint._operator_right(m,side,h).items():
        local._add(answer,key,dipole.ComplexRadical(0,1)*value)
    return answer


def _projector(line):
    return {(i,i):dipole.ComplexRadical(1) for i,s in enumerate(dipole.STATES) if s.family==line}


def _commutator(a,b):
    answer=dipole.matrix_product(a,b)
    for key,value in dipole.matrix_product(b,a).items():
        local._add(answer,key,-value)
    return answer


def _phase_data(parent,index):
    _require(type(index) is int and 0<=index<len(parent['compiled_first_poll_cells']),'original PRM source cell required')
    cell=parent['compiled_first_poll_cells'][index]
    frame=cell['persistent_cell']['incoming_state']
    _require(frame['field_mode']=='native','the exact carrier source requires the original native field')
    owner=atomic.MunichAtomicProgramme.from_record(parent['persistent_source']['atomic_owner'])
    base=atomic.MunichAtomicProgramme.atomic_base(owner)
    rule=parent['initial_poll_rule'];phases=[];programmes=[];carriers={}
    for side in (0,1):
        drives=tuple(atomic.Drive.from_record(r) for r in parent['persistent_source']['drives'][side])
        if not rule['cooling_mask'][side]:
            drives=tuple(atomic.Drive(d.role,d.beam,0,d.detuning,d.polarization) for d in drives)
        phase=atomic.MunichAtomicProgramme.phase(owner,'native',side,Q(1,25),drives)
        programme=atomic.AtomicPhase.programme(phase)
        active=[tone for tone in programme.tones if any(programme._excitation(tone).values())]
        for line in dipole.EXCITED_J:
            tones=[tone for tone in active if tone.line==line]
            _require(len(tones)<=1,'this source requires at most one active original tone per D line and side')
            if tones:
                frequency=tones[0].angular_frequency
                _require(line not in carriers or carriers[line]==frequency,
                         'shared resolved APD jumps require the same active line carrier on both sides')
                carriers[line]=frequency
        phases.append(atomic.AtomicPhase.record(phase));programmes.append(programme)
    frequencies={line:carriers.get(line,Q(0)) for line in dipole.EXCITED_J}
    projectors={line:_projector(line) for line in dipole.EXCITED_J}
    proofs=[];segments=[];zeeman=[];hamiltonians=[]
    width=Q(cell['persistent_cell']['duration'])
    for side,programme in enumerate(programmes):
        z=atomic.AtomicBase.off_diagonal_zeeman(base,side)
        static=multitone._sum(programme.static,z)
        excitation={};fields={line:dict.fromkeys(dipole.Q_COMPONENTS,ZERO) for line in dipole.EXCITED_J}
        for tone in programme.tones:
            value=programme._excitation(tone)
            if not any(value.values()):
                continue
            for q,v in tone.field.items():
                fields[tone.line][q]+=v
            excitation=multitone._sum(excitation,value)
            _require(_commutator(projectors[tone.line],value)==value,
                     'the original optical tone is not a line-projector raising operator')
            for other in projectors:
                if other!=tone.line:
                    _require(not _commutator(projectors[other],value),'the tone crosses an unregistered line frame')
        for line,p in projectors.items():
            _require(dipole.matrix_product(p,p)==p and p==dipole.matrix_adjoint(p) and not _commutator(p,static),
                     'original full hyperfine/Zeeman source does not commute with its line projector')
        detunings={state:(programme.base.detunings[state] if state in programme.base.detunings else
                         programme.base.detunings[state.family,state.f])+frequencies.get(state.family,Q(0))
                   for state in dipole.STATES}
        segment=replace(programme.base,duration=width,detunings=detunings,fields_r=fields['D1'],fields_c=fields['D2'])
        atom=joint._source(segment)
        h=multitone._sum(atom.hamiltonian,z)
        expected=dict(static)
        expected=multitone._sum(expected,excitation)
        expected=multitone._sum(expected,dipole.matrix_adjoint(excitation))
        for line,p in projectors.items():
            expected=multitone._sum(expected,multitone._scale(p,-frequencies[line]))
        _require(h==expected and h==dipole.matrix_adjoint(h),'exact full33 transformed Hamiltonian identity failed')
        for jump in atom.jumps:
            line=jump.label[0]
            _require(_commutator(projectors[line],jump.matrix)==multitone._scale(jump.matrix,-1),
                     'a resolved source jump has no single original line phase')
        capture=trap.ReloadSource.from_record(parent['persistent_source']['capture_sources'][side])
        for jump in capture.birth_operators.values():
            _require(all(not _commutator(p,jump) for p in projectors.values()),
                     'capture does not commute with the source line frame')
        segments.append(segment);zeeman.append(z);hamiltonians.append(h)
        proofs.append({'side':side,'full33_transformed_H':channel._input_record(h),
            'full_off_diagonal_Zeeman_in_generator':channel._input_record(z),
            'resolved_jump_line_phases':[[list(j.label),str(frequencies[j.label[0]])] for j in atom.jumps],
            'capture_jumps':[channel._input_record(j) for j in capture.birth_operators.values()]})
    original=joint.JointCounterGenerator.from_record(parent['persistent_source']['shared_APD']['original_shared_source'])
    collection={tuple(row['label']):tuple(tuple(channel._complex_record(v) for v in r) for r in row['matrix'])
                for row in original.record()['collection']}
    raw=joint.JointCounterGenerator(*segments,threshold=rule['threshold'],background_rate=original.background_rate,collection=collection)
    return {'schema':SCHEMA+'/constant-source-cell','source_cell_index':index,'source_start':cell['start'],'source_stop':cell['stop'],
        'source_phase_start':frame['phase_started_at'],'original_phases':phases,
        'line_carrier_reciprocal_source_units':{line:str(w) for line,w in frequencies.items()},
        'line_projectors':{line:channel._input_record(p) for line,p in projectors.items()},
        'full_source_square':proofs,'constant_counter_source':raw.record(),
        'capture_sources':parent['persistent_source']['capture_sources'],'capture_enabled':cell['persistent_cell']['capture_enabled'],
        'counter_before_cell_is_forgotten':cell['count_before_cell_is_forgotten'],
        'source_model_delta':'0','mean_field_source_used':False,
        'source_equation':'rho_frame=U^dag rho_original U; H_frame=H0+Z-Omega+A+A^dag',
        'shared_APD_phase_rule':'each original resolved D_shared is multiplied by one common line phase',
        'BG_identity_and_unobserved_capture_unchanged':True,'controller_advance':False}


class _ConstantSource:
    def __init__(self,cell):
        self.raw=joint.JointCounterGenerator.from_record(cell['constant_counter_source'])
        self.z=tuple(_read(p['full_off_diagonal_Zeeman_in_generator']) for p in cell['full_source_square'])
        self.captures=tuple(trap.ReloadSource.from_record(r) for r in cell['capture_sources'])
        self.enabled=tuple(cell['capture_enabled'])
        self.duration,self.threshold=self.raw.duration,self.raw.threshold

    def action(self,state):
        answer=self.raw.action(state)
        for count,block in self.raw._blocks(state).items():
            for side,z in enumerate(self.z):
                for key,v in _commute(z,block,side).items():
                    local._add(answer,(count,*key),v)
            for key,v in persistent._capture_action(block,self.captures,self.enabled).items():
                local._add(answer,(count,*key),v)
        return answer


class SourceKernel(channel.SourceKernel):
    def __init__(self,source,index,coefficient_bits=160):
        _require(type(source) is NativeToneFrame,'closed original tone-frame owner required; arbitrary G is not input')
        _require(type(coefficient_bits) is int and 64<=coefficient_bits<=512,'registered source coefficient precision required')
        self.source=_ConstantSource(NativeToneFrame.whole_cell(source) if index is None else NativeToneFrame.cell(source,index))
        self.dimension,self.threshold,self.bits=joint.DIMENSION,self.source.threshold,coefficient_bits
        self.columns,self.exact_columns,self.errors={},{},{}


def _frequency(record,index):
    w={line:Q(value) for line,value in record['line_carrier_reciprocal_source_units'].items()}
    return sum((w.get(dipole.STATES[i].family,Q(0)) for i in divmod(index,full.DIMENSION)),Q(0))


def _rotate(state,cell,clock,sign,bits):
    age=Q(clock)-Q(cell['source_phase_start']);result={};error=Q(0);phases={}
    for (count,i,j),v in state.items():
        frequency=_frequency(cell,i)-_frequency(cell,j)
        if frequency not in phases:
            scalar,radius=modes.complex_exponential(0,sign*frequency*age,bits=bits) if frequency*age else ((1,0),Q(0))
            phases[frequency]=(dipole.ComplexRadical(*scalar),radius)
        phase,radius=phases[frequency];local._add(result,(count,i,j),phase*v)
        error+=radius*bsm._entry_norm({(i,j):v},bits=bits)
    return result,error


def _centre(state,bits):
    result={};error=Q(0)
    for key,v in state.items():
        a,da=full.radical_midpoint(v.real,bits);b,db=full.radical_midpoint(v.imag,bits)
        channel._add(result,key,a,b);error+=da+db
    return result,error


def _counter_record(state):
    return [[c,i,j,value.serialize()] for (c,i,j),value in sorted(state.items())]


def _read_counter(record):
    return {(c,i,j):channel._complex_record(v) for c,i,j,v in record}


class NativeToneFrame:
    def __init__(self,mother):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('native tone-frame executed source closure changed')
        _guard()
        _require(type(mother) is ready.PersistentReadyMother,'source-issued original PRM required; a target Ready state is not input')
        parent=ready.PersistentReadyMother.record(mother)
        _require(parent['incoming_state']['field_mode']=='native','original native Ready inlet required')
        # One independently closed PRM is snapshotted.  Later cells do not
        # replay or numerically reverify all of its ancestors.
        first=_phase_data(parent,0)
        self._frame={'schema':SCHEMA,'original_PRM_source':parent,'first_constant_source':first,
            'whole_native_time_and_queue_mother':parent['whole_time_measure_recipe'],
            'original_stopping_source':parent['stopping'],'source_bindings':_bindings(),
            'actual_hardware_identified':False,'controller_advance':False}
        self._seal=_digest(self._frame);_ISSUED.add(self._seal)

    def record(self):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('native tone-frame executed source closure changed')
        _guard()
        _require(type(self) is NativeToneFrame and set(vars(self))=={'_frame','_seal'} and self._seal in _ISSUED and
                 _digest(self._frame)==self._seal and self._frame['source_bindings']==_bindings(),'native frame/source/clock/callback changed')
        return _copy(self._frame)

    @classmethod
    def from_record(cls,record):
        _require(cls is NativeToneFrame and type(record) is dict and record.get('schema')==SCHEMA,'closed native tone-frame source required')
        result=cls(ready.PersistentReadyMother.from_record(record['original_PRM_source']))
        _require(result.record()==record,'the original native source occurrence or exact frame changed')
        return result

    def cell(self,index):
        record=NativeToneFrame.record(self)
        return _phase_data(record['original_PRM_source'],index)

    def whole_cell(self):
        record=NativeToneFrame.record(self);parent=record['original_PRM_source'];geometry=parent['first_poll_geometry']
        _require(geometry['new_arrival_count_gate']==geometry['start'],
                 'a later rolling-count gate requires its original source counter-forgetting boundary')
        cell=_copy(record['first_constant_source'])
        first=parent['compiled_first_poll_cells'][0]['persistent_cell']['incoming_state']
        for c in parent['compiled_first_poll_cells']:
            frame=c['persistent_cell']['incoming_state']
            _require(frame['phase_started_at']==first['phase_started_at'] and frame['stage']==first['stage'] and
                     c['persistent_cell']['capture_enabled']==cell['capture_enabled'] and not c['count_before_cell_is_forgotten'],
                     'the original PC/phase/capture/count controls change inside the proposed constant source')
        cell['source_start'],cell['source_stop']=geometry['start'],geometry['poll']
        raw=cell['constant_counter_source'];width=Q(geometry['poll'])-Q(geometry['start'])
        raw['duration']=str(width)
        for atom in raw['programmes']:
            atom['duration']=str(width)
        _require(joint.JointCounterGenerator.from_record(raw).record()==raw,
                 'constant-source duration and every original derived counter field must agree')
        cell['source_cell_index']=None
        cell['numeric_midpoint_partition_collapsed_by_exact_same_source_action']=True
        return cell

    def action_column(self,index,key):
        kernel=SourceKernel(self,index,96);kernel.column(tuple(key))
        return _counter_record(kernel.exact_columns[tuple(key)])

    def transport_column(self,row,column,clock,*,to_original=False,bits=160):
        record=NativeToneFrame.record(self);parent=record['original_PRM_source'];geometry=parent['first_poll_geometry']
        clock=full.exact(clock)
        _require(type(row) is int and type(column) is int and 0<=row<joint.DIMENSION and 0<=column<joint.DIMENSION and
                 Q(geometry['start'])<=clock<=Q(geometry['poll']) and type(to_original) is bool,'original full-pair source column and source clock required')
        image,error=_rotate({(0,row,column):dipole.ComplexRadical(1)},record['first_constant_source'],clock,-1 if to_original else 1,bits)
        return {'source_record':record,'source_column':[row,column],'source_clock':str(clock),'to_original':to_original,
            'complete_pair_column':channel._input_record({(i,j):v for (c,i,j),v in image.items()}),'trace_norm_error':str(error),'scalar_bits':bits}

    def rotate_trial(self,index,pieces,*,mode_bits=60,exponential_bits=160):
        """Generate an untrusted trial; the actual constant source checks it."""
        cell=NativeToneFrame.whole_cell(self) if index is None else NativeToneFrame.cell(self,index)
        quantum=1<<mode_bits;elapsed=Q(0);result=[]
        _require(type(pieces) is list,'untrusted original source curve pieces required')
        for piece in pieces:
            width=full.nonnegative(piece['duration']);groups={}
            for mode in piece['modes']:
                for degree,coefficient in enumerate(mode['coefficients']):
                    for c,i,j,a,b in coefficient:
                        frequency=_frequency(cell,i)-_frequency(cell,j)
                        angle=frequency*(Q(cell['source_start'])+elapsed-Q(cell['source_phase_start']))
                        phase,_=modes.complex_exponential(0,angle,bits=exponential_bits) if angle else ((1,0),Q(0))
                        shifted=(mode['lambda'][0],mode['lambda'][1]+round(frequency*quantum))
                        polynomials=groups.setdefault(shifted,[{} for _ in mode['coefficients']])
                        if len(polynomials)<len(mode['coefficients']):
                            polynomials.extend({} for _ in range(len(mode['coefficients'])-len(polynomials)))
                        real=round(a*phase[0]-b*phase[1]);imag=round(a*phase[1]+b*phase[0])
                        old=polynomials[degree].get((c,i,j),(0,0));polynomials[degree][c,i,j]=(old[0]+real,old[1]+imag)
            result.append({'duration':str(width),'modes':[{'lambda':list(lam),'coefficients':[
                [[c,i,j,a,b] for (c,i,j),(a,b) in sorted(poly.items()) if a or b] for poly in polynomials]}
                for lam,polynomials in sorted(groups.items())]})
            elapsed+=width
        _require(elapsed==Q(cell['source_stop'])-Q(cell['source_start']),'trial must cover the original entire native source cell')
        return result

    def taylor_trial(self,*,order=48,mode_bits=160,coefficient_bits=192,exponential_bits=192):
        """Forward source recurrence emits a witness, never its own certificate."""
        _require(type(order) is int and 1<=order<=64 and type(mode_bits) is int and 32<=mode_bits<=256,
                 'finite source Taylor order and registered dyadic trial precision required')
        record=NativeToneFrame.record(self);cell=NativeToneFrame.whole_cell(self)
        inlet=record['original_PRM_source']['incoming_state']
        initial={(0,i,j):v for (i,j),v in channel._read_input(inlet['quantum_centre'],joint.DIMENSION).items()}
        initial,_=_rotate(initial,cell,cell['source_start'],1,exponential_bits)
        term,_=_centre(initial,coefficient_bits);kernel=SourceKernel(self,None,coefficient_bits)
        width=kernel.source.duration;quantum=1<<mode_bits;polynomials=[]
        for degree in range(order+1):
            polynomials.append([[c,i,j,round(a*quantum),round(b*quantum)] for (c,i,j),(a,b) in sorted(term.items())
                                if round(a*quantum) or round(b*quantum)])
            if degree<order:
                term={key:(width*a/(degree+1),width*b/(degree+1)) for key,(a,b) in kernel.action(term).items()}
        return [{'duration':str(width),'modes':[{'lambda':[0,0],'coefficients':polynomials}]}]

    def _certify(self,index,pieces,initial,old,precision):
        cell=NativeToneFrame.whole_cell(self) if index is None else NativeToneFrame.cell(self,index)
        kernel=SourceKernel(self,index,precision['coefficient_bits'])
        if cell['counter_before_cell_is_forgotten']:
            forgotten={}
            for (_,i,j),v in initial.items():
                local._add(forgotten,(0,i,j),v)
            initial=forgotten
        initial_frame,initial_rotation=_rotate(initial,cell,cell['source_start'],1,precision['exponential_bits'])
        centre,rounding=_centre(initial_frame,precision['coefficient_bits']);local_error=initial_rotation+rounding
        elapsed=Q(0);prices=[]
        for piece in pieces:
            width,begin,end,errors,diagnostics=channel._piece(kernel,piece,precision['mode_bits'],precision['exponential_bits'])
            gap=channel._difference(begin,centre);local_error+=gap+sum(errors.values(),Q(0));elapsed+=width
            _require(elapsed<=kernel.source.duration,'frame trial exceeds the original source cell')
            prices.append({'duration':str(width),'initial_join_error':str(gap),**{k:str(v) for k,v in errors.items()},'modes':diagnostics})
            centre=end
        _require(elapsed==kernel.source.duration,'frame trial must cover the original source cell')
        endpoint={(c,i,j):dipole.ComplexRadical(a,b) for (c,i,j),(a,b) in centre.items()}
        original,endpoint_error=_rotate(endpoint,cell,cell['source_stop'],-1,precision['exponential_bits']);local_error+=endpoint_error
        return {'cell_record':cell,'untrusted_frame_curve':_copy(pieces),'precision':precision,'source_cell_index':index,
            'physical_input_centre':_counter_record(initial),'physical_counter_endpoint':_counter_record(original),
            'frame_counter_endpoint':_counter_record(endpoint),'upstream_error_once':str(old),
            'initial_frame_scalar_error':str(initial_rotation),'initial_radical_error':str(rounding),
            'endpoint_physical_frame_scalar_error':str(endpoint_error),'piece_error_records':prices,
            'source_model_payment':'0','new_local_error':str(local_error),'global_error':str(old+local_error),
            'source_columns_checked':len(kernel.columns),'source_model_removed_by_exact_action_square':True}

    def certify_first_cell(self,pieces,*,mode_bits=60,coefficient_bits=160,exponential_bits=160):
        record=NativeToneFrame.record(self);inlet=record['original_PRM_source']['incoming_state']
        initial={(0,i,j):v for (i,j),v in channel._read_input(inlet['quantum_centre'],joint.DIMENSION).items()}
        report=NativeToneFrame._certify(self,0,pieces,initial,Q(inlet['global_error']),
            dict(mode_bits=mode_bits,coefficient_bits=coefficient_bits,exponential_bits=exponential_bits))
        report.update({'schema':SCHEMA+'/first-cell-coimage','source_record':record,
            'whole_native_time_and_queue_mother':record['whole_native_time_and_queue_mother'],
            'physical_endpoint_is_original_full_pair':True,'target_Ready_input':False,'controller_advance':False})
        _REPORTS.add(_digest(report));return report

    def verify_first_cell(self,report):
        record=NativeToneFrame.record(self)
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/first-cell-coimage' and report['source_record']==record,
                 'same original PRM and exact frame report required')
        expected=NativeToneFrame.certify_first_cell(self,report['untrusted_frame_curve'],**report['precision'])
        _require(report==expected,'original action residual, endpoint frame, old error or source model payment changed')
        return True

    def certify_first_poll(self,pieces,*,mode_bits=60,coefficient_bits=160,exponential_bits=160):
        """Original first PC poll, using the exact whole constant frame source."""
        record=NativeToneFrame.record(self);parent=record['original_PRM_source'];inlet=parent['incoming_state']
        initial={(0,i,j):v for (i,j),v in channel._read_input(inlet['quantum_centre'],joint.DIMENSION).items()}
        report=NativeToneFrame._certify(self,None,pieces,initial,Q(inlet['global_error']),
            dict(mode_bits=mode_bits,coefficient_bits=coefficient_bits,exponential_bits=exponential_bits))
        states=_read_counter(report['physical_counter_endpoint']);old_count=len(parent['first_poll_geometry']['surviving_old_arrival_word'])
        rule=parent['initial_poll_rule'];rules={r['name']:r for r in parent['persistent_source']['rules']}
        ready_state={};pending={};faces=[]
        for count in range(rule['threshold']+1):
            matrix={(i,j):v for (c,i,j),v in states.items() if c==count}
            high=old_count+count>=rule['threshold'];stage=rule['high_next'] if high else rule['low_next']
            changes=rule['high_flags'] if high else rule['low_flags']
            flags=[before if after is None else after for before,after in zip(inlet['loaded_flags'],changes)]
            target=ready_state if rules[stage]['ready'] else pending
            for key,v in matrix.items():
                local._add(target,key,v)
            faces.append({'capped_new_count':count,'rolling_count_at_least_threshold':high,'PC_stage':stage,
                'loaded_flags':flags,'PC_ready':rules[stage]['ready'],'poststate':channel._input_record(matrix)})
        trace=joint._trace(ready_state)
        _require(not trace.imag,'source-issued Hermitian Ready trace required')
        mass,radical_error=full.radical_midpoint(trace.real,coefficient_bits);error=Q(report['global_error'])
        normalizer={'centre':str(mass),'radical_rounding':str(radical_error),
            'lower':str(max(Q(0),mass-radical_error-error)),
            'upper':str(min(Q(parent['positive_source_input_mass_upper']),mass+radical_error+error)),
            'strictly_positive':mass-radical_error-error>0,'supplied_by_caller':False,
            'origin':'trace of the original count-PC ready CP coimage with its complete source residual price'}
        report.update({'schema':SCHEMA+'/first-poll-coimage','source_record':record,'count_faces':faces,
            'generated_first_ready_poststate':channel._input_record(ready_state),'first_poll_pending_poststate':channel._input_record(pending),
            'first_poll_joint_error':report['global_error'],'original_PC_poll_and_rolling_queue':parent['first_poll_geometry'],
            'source_ready_normalizer':normalizer,
            'whole_native_time_and_queue_mother':record['whole_native_time_and_queue_mother'],
            'whole_stopping':record['original_stopping_source'],'source_positive_input_mass_upper':parent['positive_source_input_mass_upper'],
            'capture_or_physical_occupancy_declared_ready':False,'ready_is_original_count_PC_confirmation':True,
            'time_resolved_numerical_measure_certified':False,'target_Ready_input':False,'controller_advance':False})
        _REPORTS.add(_digest(report));return report

    def verify_first_poll(self,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/first-poll-coimage' and
                 report['source_record']==NativeToneFrame.record(self),'same original native first-poll source required')
        expected=NativeToneFrame.certify_first_poll(self,report['untrusted_frame_curve'],**report['precision'])
        _require(expected==report,'exact native source, full Ready/pending coimage, queue/PC poll or error changed')
        return True


def _function(f):
    f=getattr(f,'__func__',f)
    return id(f),id(getattr(f,'__code__',None))


def _execution():
    functions=(_require,_copy,_digest,_bindings,_read,_commute,_projector,_commutator,_phase_data,
        _frequency,_rotate,_centre,_counter_record,_read_counter,_function,_execution,_guard,
        ready.PersistentReadyMother.record,ready.PersistentReadyMother.from_record,
        persistent._capture_action,atomic.AtomicPhase.record,atomic.AtomicPhase.programme,
        atomic.MunichAtomicProgramme.record,atomic.MunichAtomicProgramme.from_record,atomic.MunichAtomicProgramme.phase,
        atomic.AtomicBase.off_diagonal_zeeman,atomic.MunichAtomicProgramme.atomic_base,
        joint.JointCounterGenerator.action,joint.JointCounterGenerator.from_record,
        joint.JointCounterGenerator._blocks,joint.JointCounterGenerator.detected_action,
        joint.JointCounterGenerator.independent_atomic_action,
        joint._operator_left,joint._operator_right,local._add,local._sum,
        channel._piece,channel._difference,channel._read_input,channel._input_record,channel._complex_record,
        channel._coefficient,channel._entry_norm,channel._hermitian,channel._add,channel._key,
        local.CounterGenerator.atomic_action,local.CounterGenerator._drift,local._apply_recycling,
        full.radical_midpoint,modes.complex_exponential,bsm._entry_norm,
        dipole.matrix_product,dipole.matrix_adjoint,multitone.Programme._excitation,
        channel.SourceKernel.column,channel.SourceKernel.action,channel.SourceKernel.coefficient_error)
    methods=tuple(_function(member) for cls in (NativeToneFrame,_ConstantSource,SourceKernel) for member in vars(cls).values()
                  if callable(member) or isinstance(member,(classmethod,staticmethod)))
    return tuple(map(_function,functions)),methods,tuple(dipole.STATES),tuple(dipole.INDEX.items()),tuple(dipole.Q_COMPONENTS),SCHEMA,joint.DIMENSION


def _guard():
    if _execution is not _EXECUTION or _execution.__code__ is not _EXECUTION_CODE or _execution()!=_EXPECTED:
        raise ValueError('native tone-frame executed source closure changed')


_EXECUTION,_EXECUTION_CODE=_execution,_execution.__code__
_GUARD,_GUARD_CODE=_guard,_guard.__code__
_EXPECTED=_execution()
