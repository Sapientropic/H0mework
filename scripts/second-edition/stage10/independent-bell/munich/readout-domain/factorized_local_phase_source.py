"""Same native Ready, exact local actions, complete Hermitian tensor coimage.

Only the representation changes: a source-issued full pair is decomposed
exactly, each small factor is propagated by the original raw local CP law,
and the complete pair is expanded once after both original local plans.
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
import instrument_history as instrument
import munich_atomic_programme as atomic
import native_tone_frame as native
import exact_local_phase_source as exact
import bsm_retry_source as bsm


SCHEMA='stage10-factorized-exact-raw-local-phase-source/v1'
ZERO=dipole.ComplexRadical()
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
        (dipole,full,channel,local,joint,instrument,atomic,native,exact,bsm)))
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _add(target,matrix,coefficient=1):
    for key,value in matrix.items():
        local._add(target,key,coefficient*value)


def _tensor(first,second):
    # The native numerical coimage and all checked local endpoints are
    # rational.  Use the existing full operator tensor without projection.
    try:
        a={k:(v.real.as_rational(),v.imag.as_rational()) for k,v in first.items()}
        b={k:(v.real.as_rational(),v.imag.as_rational()) for k,v in second.items()}
    except ValueError:
        return {(joint.atom_pair_index(a,b),joint.atom_pair_index(c,d)):x*y
                for (a,c),x in first.items() for (b,d),y in second.items() if x*y}
    return {k:dipole.ComplexRadical(*v) for k,v in instrument._tensor(a,b).items()}


def _decompose(matrix):
    matrix=channel._initial(matrix,joint.DIMENSION)
    blocks={}
    for (row,column),value in matrix.items():
        a,b=divmod(row,full.DIMENSION);c,d=divmod(column,full.DIMENSION)
        local._add(blocks.setdefault((a,c),{}),(b,d),value)
    terms=[]
    for a in range(full.DIMENSION):
        block=blocks.get((a,a),{})
        if block:
            terms.append(({(a,a):dipole.ComplexRadical(1)},block))
        for c in range(a+1,full.DIMENSION):
            forward,reverse=blocks.get((a,c),{}),blocks.get((c,a),{})
            if not forward and not reverse:
                continue
            real,imag={},{}
            _add(real,forward,Q(1,2));_add(real,reverse,Q(1,2))
            _add(imag,forward,dipole.ComplexRadical(0,Q(-1,2)))
            _add(imag,reverse,dipole.ComplexRadical(0,Q(1,2)))
            if real:
                terms.append(({(a,c):dipole.ComplexRadical(1),(c,a):dipole.ComplexRadical(1)},real))
            if imag:
                terms.append(({(a,c):dipole.ComplexRadical(0,1),(c,a):dipole.ComplexRadical(0,-1)},imag))
    reconstructed={}
    for first,second in terms:
        _require(first==dipole.matrix_adjoint(first) and second==dipole.matrix_adjoint(second),
                 'source-generated tensor factors must be Hermitian')
        _add(reconstructed,_tensor(first,second))
    _require(reconstructed==matrix,'complete source tensor decomposition lost a coordinate or coherence')
    return terms


def _factor_inventory(terms):
    factors=({},{});indices=[]
    for first,second in terms:
        ids=[]
        for side,matrix in enumerate((first,second)):
            record=channel._input_record(matrix);identity=_digest(record)
            _require(identity not in factors[side] or factors[side][identity]==record,'factor identity collision')
            factors[side][identity]=record;ids.append(identity)
        indices.append(ids)
    return [[{'factor_id':identity,'initial_local_matrix':record}
             for identity,record in sorted(side.items())] for side in factors],indices


def _plans(owner,plans):
    _require(type(plans) in (tuple,list) and len(plans)==2,'two original raw local clock plans required')
    parent=atomic.MunichAtomicProgramme.record(owner);result=[]
    for side,plan in enumerate(plans):
        _require(type(plan) in (tuple,list) and len(plan)>=3,'alternating preparation then excitation is required on each side')
        cleaned=[];previous=None
        for index,item in enumerate(plan):
            _require(type(item) is dict and set(item)=={'phase','cuts'},'only original phase and complete raw clock cuts are inputs')
            phase=atomic._read_phase(item['phase']);raw=atomic.AtomicPhase.record(phase)
            kind='excitation' if index==len(plan)-1 else 'preparation'
            _require(raw['parent']==parent and raw['side']==side and raw['kind']==kind,
                     'raw local plan belongs to another owner, side or laser role')
            if kind=='preparation':
                pump=next(d for d in raw['drives'] if d['role']=='pump2to1')
                current=pump['beam'],pump['polarization']
                _require(previous is None or all(a!=b for a,b in zip(previous,current)),
                         'the original pump direction and polarization must alternate')
                previous=current
            cuts=tuple(map(full.exact,item['cuts']));duration=atomic.AtomicPhase.programme(phase).base.duration
            _require(len(cuts)>=2 and cuts[0]==0 and cuts[-1]==duration and all(a<b for a,b in zip(cuts,cuts[1:])),
                     'raw local cuts must cover the complete original phase clock')
            cleaned.append({'phase':raw,'cuts':list(map(str,cuts))})
        result.append(cleaned)
    return result


def _embed(matrix,side):
    return {(joint.atom_pair_index(a,dipole.ION),joint.atom_pair_index(b,dipole.ION)):v
            for (a,b),v in matrix.items()} if side==0 else {
                (joint.atom_pair_index(dipole.ION,a),joint.atom_pair_index(dipole.ION,b)):v
                for (a,b),v in matrix.items()}


def _unembed(matrix,side):
    result={}
    for (row,column),value in matrix.items():
        a,b=divmod(row,full.DIMENSION);c,d=divmod(column,full.DIMENSION)
        _require((b,d)==(dipole.ION,dipole.ION) if side==0 else (a,c)==(dipole.ION,dipole.ION),
                 'original local TP action changed its exact identity spectator')
        local._add(result,(a,c) if side==0 else (b,d),value)
    _require(result==dipole.matrix_adjoint(result),'complete local Hermitian endpoint required')
    return result


def _cells(plan):
    return [(index,cell,atomic._read_phase(item['phase']),(Q(a),Q(b)))
            for index,item in enumerate(plan) for cell,(a,b) in enumerate(zip(item['cuts'],item['cuts'][1:]))]


def _trial_endpoint(trial,mode_bits,side):
    # This producer readout seeds the next untrusted trial.  The independent
    # checker reconstructs every endpoint from the original G(t) instead.
    _require(len(trial)==1 and trial[0]['duration']=='1' and len(trial[0]['modes'])==1 and
             trial[0]['modes'][0]['lambda']==[0,0],'source-generated polynomial trial required')
    centre={};quantum=1<<mode_bits
    for coefficient in trial[0]['modes'][0]['coefficients']:
        for c,i,j,a,b in coefficient:
            channel._add(centre,(c,i,j),Q(a,quantum),Q(b,quantum))
    centre=channel._hermitian(centre)
    return _unembed({(i,j):dipole.ComplexRadical(a,b) for (c,i,j),(a,b) in centre.items()},side)


def _norm(matrix,bits):
    return bsm._entry_norm(matrix,bits=bits)


def _tensor_price(first,second,ea,eb,bits):
    na,nb=_norm(first,bits),_norm(second,bits)
    return ea*nb+eb*na+ea*eb,na,nb


def _expand(terms):
    result={}
    for term in terms:
        first=channel._read_input(term['left']['local_poststate'],full.DIMENSION)
        second=channel._read_input(term['right']['local_poststate'],full.DIMENSION)
        _add(result,_tensor(first,second))
    _require(result==dipole.matrix_adjoint(result),'complete tensor endpoint is not Hermitian')
    return result


class FactorizedLocalPhaseSource:
    def __init__(self,frame,ready_report,local_clock_plan):
        if _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
            raise ValueError('factorized local executed source closure changed')
        _CHECK()
        _require(type(frame) is native.NativeToneFrame,'closed source-issued NativeToneFrame required; a target Ready is not input')
        parent=native.NativeToneFrame.record(frame)
        native.NativeToneFrame.verify_first_poll(frame,ready_report)
        owner=atomic.MunichAtomicProgramme.from_record(parent['original_PRM_source']['persistent_source']['atomic_owner'])
        matrix=channel._read_input(ready_report['generated_first_ready_poststate'],joint.DIMENSION)
        factors,terms=_factor_inventory(_decompose(matrix));plans=_plans(owner,local_clock_plan)
        self._frame={'schema':SCHEMA,'native_source_record':parent,'native_ready_report':_copy(ready_report),
            'common_atomic_owner':atomic.MunichAtomicProgramme.record(owner),'raw_two_local_clock_plan':plans,
            'complete_initial_ready':channel._input_record(matrix),'upstream_trace_norm_error':ready_report['first_poll_joint_error'],
            'initial_source_ready_normalizer':_copy(ready_report['source_ready_normalizer']),
            'local_factor_inventory':factors,'source_tensor_factor_ids':terms,
            'whole_native_time_and_queue_mother':_copy(parent['whole_native_time_and_queue_mother']),
            'native_ready_count_faces':_copy(ready_report['count_faces']),
            'native_pending_poststate':_copy(ready_report['first_poll_pending_poststate']),
            'seconds_per_source_unit':owner.record()['atomic_base']['seconds_per_unit'],
            'tensor_identity':'complete initial Ready = sum of the source-generated Hermitian A_j tensor B_j',
            'factor_positivity_assumed':False,'initial_ready_was_normalized_here':False,
            'actual_hardware_uniquely_identified':False,'controller_advance':False,'source_bindings':_bindings()}
        self._seal=_digest(self._frame);_ISSUED.add(self._seal)

    def record(self):
        if _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
            raise ValueError('factorized local executed source closure changed')
        _CHECK()
        _require(type(self) is FactorizedLocalPhaseSource and set(vars(self))=={'_frame','_seal'} and
                 self._seal in _ISSUED and _digest(self._frame)==self._seal and self._frame['source_bindings']==_bindings(),
                 'factorized original source, clock plans, occurrence or snapshot changed')
        return _copy(self._frame)

    def with_clock_plan(self,local_clock_plan):
        record=FactorizedLocalPhaseSource.record(self)
        owner=atomic.MunichAtomicProgramme.from_record(record['common_atomic_owner'])
        record['raw_two_local_clock_plan']=_plans(owner,local_clock_plan)
        result=object.__new__(FactorizedLocalPhaseSource)
        result._frame=record;result._seal=_digest(record);_ISSUED.add(result._seal)
        return result

    @classmethod
    def from_record(cls,record):
        _require(cls is FactorizedLocalPhaseSource and type(record) is dict and record.get('schema')==SCHEMA,
                 'closed factorized native/local source record required')
        result=cls(native.NativeToneFrame.from_record(record['native_source_record']),record['native_ready_report'],
                   record['raw_two_local_clock_plan'])
        _require(FactorizedLocalPhaseSource.record(result)==record,'factor decomposition or original source lineage changed')
        return result

    def generate_trials(self,*,order=24,mode_bits=160,coefficient_bits=192,exponential_bits=192,phase_order=32):
        record=FactorizedLocalPhaseSource.record(self);side_curves=[]
        precision=dict(phase_order=phase_order,mode_bits=mode_bits,coefficient_bits=coefficient_bits,exponential_bits=exponential_bits)
        for side,inventory in enumerate(record['local_factor_inventory']):
            curves=[];cells=_cells(record['raw_two_local_clock_plan'][side])
            for item in inventory:
                current=channel._read_input(item['initial_local_matrix'],full.DIMENSION);witnesses=[]
                for phase_index,cell_index,phase,interval in cells:
                    source=exact.ExactLocalPhaseSource(phase,_embed(current,side),interval=interval)
                    trial=exact.ExactLocalPhaseSource.generate_trial(source,order=order,mode_bits=mode_bits,
                        coefficient_bits=coefficient_bits,exponential_bits=exponential_bits)
                    witnesses.append(trial);current=_trial_endpoint(trial,mode_bits,side)
                curves.append({'factor_id':item['factor_id'],'cell_curves':witnesses})
            side_curves.append(curves)
        return {'schema':SCHEMA+'/untrusted-local-curves','source_record':record,'precision':precision,'side_curves':side_curves}

    def certify(self,trials):
        record=FactorizedLocalPhaseSource.record(self)
        _require(type(trials) is dict and set(trials)=={'schema','source_record','precision','side_curves'} and
                 trials['schema']==SCHEMA+'/untrusted-local-curves' and trials['source_record']==record and
                 type(trials['side_curves']) is list and len(trials['side_curves'])==2,
                 'complete untrusted curves for this original factorized source required')
        precision=trials['precision']
        _require(type(precision) is dict and set(precision)=={'phase_order','mode_bits','coefficient_bits','exponential_bits'},
                 'complete registered exact local precision required')
        endpoints=[{},{}];local_records=[[],[]]
        for side,inventory in enumerate(record['local_factor_inventory']):
            supplied=trials['side_curves'][side]
            _require(type(supplied) is list and [x.get('factor_id') for x in supplied]==[x['factor_id'] for x in inventory],
                     'every original factor needs exactly one complete source witness')
            cells=_cells(record['raw_two_local_clock_plan'][side])
            for item,witness in zip(inventory,supplied):
                _require(set(witness)=={'factor_id','cell_curves'} and type(witness['cell_curves']) is list and
                         len(witness['cell_curves'])==len(cells),'whole original local phase clock witness required')
                current=channel._read_input(item['initial_local_matrix'],full.DIMENSION);error=Q(0);certificates=[]
                for (phase_index,cell_index,phase,interval),curve in zip(cells,witness['cell_curves']):
                    source=exact.ExactLocalPhaseSource(phase,_embed(current,side),upstream_error=error,interval=interval)
                    certificate=exact.ExactLocalPhaseSource.certify(source,curve,**precision)
                    _require(certificate['old_error_once']==str(error) and certificate['source_model_payment']=='0',
                             'the original exact local TP checker dropped a source price')
                    current=_unembed(channel._read_input(certificate['full_pair_endpoint'],joint.DIMENSION),side)
                    error=Q(certificate['trace_norm_error'])
                    certificates.append({'phase_index':phase_index,'cell_index':cell_index,'source_certificate':certificate})
                endpoint={'factor_id':item['factor_id'],'local_poststate':channel._input_record(current),'trace_norm_error':str(error)}
                endpoints[side][item['factor_id']]=endpoint
                local_records[side].append({'factor_id':item['factor_id'],'complete_local_certificates':certificates})
        old=Q(record['upstream_trace_norm_error']);error=old;terms=[]
        for left,right in record['source_tensor_factor_ids']:
            a,b=endpoints[0][left],endpoints[1][right]
            ma=channel._read_input(a['local_poststate'],full.DIMENSION);mb=channel._read_input(b['local_poststate'],full.DIMENSION)
            cost,na,nb=_tensor_price(ma,mb,Q(a['trace_norm_error']),Q(b['trace_norm_error']),precision['coefficient_bits'])
            error+=cost;terms.append({'left':a,'right':b,'local_norm_upper':[str(na),str(nb)],'tensor_error':str(cost)})
        matrix=_expand(terms)
        clocks=[sum((Q(item['phase']['duration_seconds']) for item in plan),Q(0)) for plan in record['raw_two_local_clock_plan']]
        return {'schema':SCHEMA+'/complete-local-tensor-coimage','source_record':record,'untrusted_trials':_copy(trials),
            'complete_local_factor_certificates':local_records,'tensor_terms':terms,
            'full_pair_endpoint':channel._input_record(matrix),'trace_norm_error':str(error),'old_error_once':str(old),
            'tensor_local_error':str(error-old),'source_model_payment':'0',
            'tensor_error_formula':'oldE_once + sum(eA*norm(Bcentre) + eB*norm(Acentre) + eA*eB)',
            'source_local_emission_origins_seconds':list(map(str,clocks)),
            'complete_native_time_and_queue_mother':record['whole_native_time_and_queue_mother'],
            'complete_33_squared_coordinates_retained':True,'small_terms_dropped':False,
            'factor_centres_assumed_positive':False,'target_factors_supplied_by_caller':False,
            'numerical_generation_is_independent_of_checker':True,'controller_advance':False}

    def verify(self,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/complete-local-tensor-coimage' and
                 report.get('source_record')==FactorizedLocalPhaseSource.record(self),'same original factorized local report required')
        _require(FactorizedLocalPhaseSource.certify(self,report['untrusted_trials'])==report,
                 'complete factorized poststate, source witnesses, clocks or tensor price changed')
        return True

    def poststate(self,report):
        FactorizedLocalPhaseSource.verify(self,report)
        return channel._read_input(report['full_pair_endpoint'],joint.DIMENSION),Q(report['trace_norm_error'])


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _execution():
    functions=(_require,_copy,_digest,_bindings,_add,_tensor,_decompose,_factor_inventory,_plans,_embed,_unembed,_cells,
        _trial_endpoint,_norm,_tensor_price,_expand,_function,_execution,_check,
        instrument._tensor,instrument.full._add,full._add,local._add,channel._canonical,channel._initial,channel._input_record,channel._read_input,
        channel._add,channel._hermitian,joint.atom_pair_index,dipole.matrix_adjoint,bsm._entry_norm,
        atomic._read_phase,atomic.MunichAtomicProgramme.record,atomic.MunichAtomicProgramme.from_record,
        atomic.AtomicPhase.record,atomic.AtomicPhase.programme,native.NativeToneFrame.record,native.NativeToneFrame.from_record,
        native.NativeToneFrame.verify_first_poll,exact.ExactLocalPhaseSource.record,exact.ExactLocalPhaseSource.generate_trial,
        exact.ExactLocalPhaseSource.certify)
    methods=tuple(_function(member) for member in vars(FactorizedLocalPhaseSource).values()
                  if callable(member) or isinstance(member,(classmethod,staticmethod)))
    return tuple(map(_function,functions)),methods,tuple(dipole.STATES),tuple(dipole.INDEX.items()),dipole.ION,full.DIMENSION,joint.DIMENSION,SCHEMA


def _check():
    if _execution is not _EXECUTION or _execution.__code__ is not _EXECUTION_CODE or _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
        raise ValueError('factorized local executed source closure changed')
    if instrument.full is not full or _execution()!=_EXPECTED or exact._guard is not exact._GUARD or exact._guard.__code__ is not exact._GUARD_CODE:
        raise ValueError('factorized local executed source closure changed')
    exact._GUARD()


_EXECUTION,_EXECUTION_CODE=_execution,_execution.__code__
_CHECK,_CHECK_CODE=_check,_check.__code__
_EXPECTED=_execution()
