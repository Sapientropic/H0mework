"""The original Ready factors flow through their complete raw local programmes.

Each next phase is issued from the preceding original-G certificate.  Numerical
phase models are shared between factors and never supply a trusted endpoint.
"""
from fractions import Fraction as Q
from pathlib import Path
import cmath
import hashlib
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import fluorescence_channel as channel
import exact_local_phase_source as exact
import factorized_local_phase_source as factors
import fourier_local_phase_source as fourier
import reference_local_phase_source as reference
import munich_atomic_programme as atomic
import bsm_retry_source as bsm


SCHEMA='stage10-reference-clock-sequential-Fourier-local-programme/v1'
PHASE_SCHEMA=SCHEMA+'/source-issued-factor-phase'
ZERO=dipole.ComplexRadical()
_ISSUED=set()
_PHASE_ISSUED=set()
_CHECKED={}
_CURVE_CHECKED={}
_MODELS={}
_TEMPLATES={}


def _require(condition,message):
    if not condition:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    modules=(dipole,full,channel,exact,factors,fourier,reference,atomic,bsm)
    paths=(Path(__file__),*(Path(m.__file__) for m in modules))
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _matrix(record):
    return channel._read_input(record,full.DIMENSION)


def _item(programme,side,factor_id):
    raw=FourierReferenceLocalProgrammeSource.record(programme)['reference_local_parent']
    _require(type(side) is int and side in (0,1),'original local side required')
    found=next((x for x in raw['local_factor_inventory'][side] if x['factor_id']==factor_id),None)
    _require(found is not None,'factor is outside the source-generated Ready inventory')
    return raw,found


def _emit_phase(programme,side,factor_id,index,current,error,prefix):
    parent,_=_item(programme,side,factor_id)
    plans=parent['source_generated_local_plans'][side]
    _require(index<len(plans),'the complete raw local programme has already ended')
    raw_phase=plans[index]['source_phase']
    phase=atomic._read_phase(raw_phase);program=atomic.AtomicPhase.programme(phase)
    source=object.__new__(_FactorPhaseSource)
    source._frame={'schema':PHASE_SCHEMA,'programme_source_digest':programme._seal,
        'side':side,'factor_id':factor_id,'phase_index':index,'source_phase':raw_phase,
        'complete_initial_local_factor':channel._input_record(current),'factor_upstream_error':str(error),
        'source_duration':str(program.base.duration),
        'original_source_frequencies':[str(t.angular_frequency) for t in program.tones],
        'physical_duration_seconds':raw_phase['duration_seconds'],
        'reference_clock':parent['reference_clock'],
        'verified_preceding_phase_certificate_digests':list(prefix),
        'phase_state_origin':'original Ready factor' if not index else 'complete preceding original-G phase coimage',
        'phase_local_elapsed_before_seconds':str(sum((Q(x['raw_controls']['duration_seconds']) for x in plans[:index]),Q(0))),
        'source_input_is_a_free_endpoint':False,'mother_error_paid_per_factor':False,'source_bindings':_bindings()}
    source._seal=_digest(source._frame);_PHASE_ISSUED.add(source._seal)
    return source


class _SequentialColumns:
    column=fourier._Columns.column
    action=fourier._Columns.action

    def __init__(self,source,bits):
        raw=_FactorPhaseSource.record(source);phase=atomic._read_phase(raw['source_phase'])
        lifted=exact.ExactLocalPhaseSource(phase,factors._embed(_matrix(raw['complete_initial_local_factor']),raw['side']))
        self.tensor=exact._TensorColumns(lifted,bits);self.side=raw['side'];self.bits=bits;self.cache={}
        self.frequencies=tuple(t.angular_frequency for t in self.tensor.programme.tones)
        self.components=tuple(self.tensor.operations)


def _certify_phase(source,pieces,precision):
    raw=_FactorPhaseSource.record(source)
    _require(type(pieces) is list and type(precision) is dict and
        set(precision)=={'mode_bits','coefficient_bits','exponential_bits'},'complete original Fourier curve precision required')
    mb,cb,eb=(precision[k] for k in ('mode_bits','coefficient_bits','exponential_bits'))
    _require(type(mb) is int and 32<=mb<=256 and type(cb) is int and 64<=cb<=512 and
        type(eb) is int and 64<=eb<=1024,'registered Fourier source precision required')
    curve_key=_digest({'source_record':raw,'pieces':pieces,'precision':precision})
    if curve_key in _CURVE_CHECKED:
        return _copy(_CURVE_CHECKED[curve_key])
    columns=_SequentialColumns(source,cb);initial=_matrix(raw['complete_initial_local_factor'])
    centre={};rounding=Q(0)
    for key,value in initial.items():
        a,ea=full.radical_midpoint(value.real,cb);b,ebound=full.radical_midpoint(value.imag,cb)
        full._add(centre,key,a,b);rounding+=ea+ebound
    error=Q(raw['factor_upstream_error'])+rounding;elapsed=Q(0);payments=[]
    for piece in pieces:
        width,begin,end,cost,details=fourier._piece(columns,piece,elapsed,mb,eb)
        gap=fourier._difference(begin,centre);error+=gap+sum(cost.values(),Q(0));elapsed+=width
        _require(elapsed<=Q(raw['source_duration']),'phase curve exceeds its original raw physical duration')
        payments.append({'join_error':str(gap),**{k:str(v) for k,v in cost.items()},**details});centre=end
    _require(elapsed==Q(raw['source_duration']),'every original raw phase must be completely covered')
    norm=bsm._entry_norm(initial,bits=cb)
    clock=reference._phase_clock_price(atomic._read_phase(raw['source_phase']),
        (Q(0),Q(raw['physical_duration_seconds'])),raw['reference_clock'],norm,cb)
    error,outward=reference._outward_error(error+Q(clock['total_trace_norm_payment']),cb)
    result={'schema':PHASE_SCHEMA+'/coimage','source_record':raw,'untrusted_curve':_copy(pieces),'precision':_copy(precision),
        'full_local_poststate':channel._input_record({k:dipole.ComplexRadical(*v) for k,v in centre.items()}),
        'trace_norm_error':str(error),'old_factor_error_once':raw['factor_upstream_error'],
        'source_reference_clock_price':clock,'error_outward_rounding':str(outward),
        'piece_error_records':payments,'original_source_columns_checked':len(columns.tensor.columns),
        'source_phase_Taylor_tail_used':False,'source_model_mean_payment':'0',
        'mode_or_graph_correctness_assumed':False,'full33_coordinates_and_outside_trial_space_priced':True}
    _CHECKED[_digest(result)]=_copy(result)
    _CURVE_CHECKED[curve_key]=_copy(result)
    return result


def _prepare_template(source,piece,precision):
    raw=_FactorPhaseSource.record(source);key=_digest({'phase':raw['source_phase'],'piece':piece,
        'precision':precision,'closure':_bindings()})
    if key in _TEMPLATES:
        return _TEMPLATES[key]
    mb,cb,eb=(precision[k] for k in ('mode_bits','coefficient_bits','exponential_bits'))
    _require(type(mb) is int and 32<=mb<=256 and type(cb) is int and 64<=cb<=512 and
        type(eb) is int and 64<=eb<=1024,'registered shared-mode precision required')
    columns=_SequentialColumns(source,cb)
    width,begin_h,end_h,prices,details,begin,end=fourier._piece(columns,piece,Q(0),mb,eb,
        return_complex_endpoints=True)
    _require(width==Q(raw['source_duration']),'shared original mode template must cover the whole phase')
    _require(all(len(mode['coefficients'])==1 for mode in piece['modes']),
        'shared numerical phase templates are constant matrix exponential modes')
    _require(fourier._hermitian(begin)==begin_h and fourier._hermitian(end)==end_h,
        'shared raw complex template endpoints disagree with the original complete Fourier curve')
    result={'begin':begin,'end':end,'error':sum(prices.values(),Q(0)),
        'certificate':{'raw_template_digest':_digest(piece),'original_source_phase':raw['source_phase'],
          'whole_source_duration':str(width),'precision':precision,
          'original_full_frequency_error_prices':{k:str(v) for k,v in prices.items()},**details,
          'complex_template_is_not_a_positive_input_state':True}}
    _TEMPLATES[key]=result;return result


def _validate_zero_template(source,piece,precision):
    raw=_FactorPhaseSource.record(source)
    _require(type(piece) is dict and set(piece)=={'duration','modes'} and
        Q(piece['duration'])==Q(raw['source_duration']) and type(piece['modes']) is list and piece['modes'],
        'zero-weight template still keeps its complete original source-time structure')
    quantum=1<<precision['mode_bits'];frequencies=tuple(map(Q,raw['original_source_frequencies']))
    for mode in piece['modes']:
        lr,_=fourier._frequency(mode,frequencies,quantum)
        _require(lr*Q(piece['duration'])<=Q(1,2) and type(mode['coefficients']) is list and mode['coefficients'],
            'zero-weight untrusted source mode structure and growth bound required')
        for matrix in mode['coefficients']:
            fourier._coefficient(matrix,quantum)


def _cp_endpoint_template(source,piece,precision):
    raw=_FactorPhaseSource.record(source);_validate_zero_template(source,piece,precision)
    quantum=1<<precision['mode_bits'];out_quantum=1<<precision['coefficient_bits']
    frequencies=tuple(map(Q,raw['original_source_frequencies']));width=Q(raw['source_duration']);begin={};end={}
    for mode in piece['modes']:
        _require(len(mode['coefficients'])==1,'constant matrix exponential CP endpoint template required')
        matrix=fourier._coefficient(mode['coefficients'][0],quantum)
        fourier._add_rational(begin,matrix,(Q(1),Q(0)))
        lr,nu=fourier._frequency(mode,frequencies,quantum)
        proposal=cmath.exp(complex(float(lr*width),float(nu*width)))
        scalar=(Q(round(proposal.real*out_quantum),out_quantum),Q(round(proposal.imag*out_quantum),out_quantum))
        fourier._add_rational(end,matrix,scalar)
    error=fourier._norm(begin)+fourier._norm(end)
    return {'begin':begin,'end':end,'error':error,'certificate':{
        'classification':'CP_endpoint_norm_enclosure','raw_template_digest':_digest(piece),
        'whole_source_duration':str(width),'entry_norm_B0':str(fourier._norm(begin)),
        'entry_norm_chosen_Qend':str(fourier._norm(end)),
        'source_CPTP_from_full_AtomicPhase':'full natural/ION GKSL and Hermitian full static/Z/tone+adjoint Hamiltonian',
        'original_source_phase':raw['source_phase'],'Qend_is_the_saved_numeric_proposal_centre':True,
        'exact_exponential_or_original_curve_residual_claimed':False}}


def _template_norm_bound(piece,precision):
    quantum=1<<precision['mode_bits']
    return sum((fourier._norm(fourier._coefficient(matrix,quantum)) for mode in piece['modes'] for matrix in mode['coefficients']),Q(0))


def _certify_shared_phase(source,witness,templates,precision):
    raw=_FactorPhaseSource.record(source)
    _require(type(templates) is list and templates and type(precision) is dict and
        set(precision)=={'mode_bits','coefficient_bits','exponential_bits'},'complete source-bound shared templates and precision required')
    _require(type(witness) is dict and set(witness)=={'template_digest','weights'} and
        witness['template_digest']==_digest(templates) and type(witness['weights']) is list and
        len(witness['weights'])==len(templates),'same original phase templates and complete untrusted complex weights required')
    key=_digest({'source_record':raw,'witness':witness,'templates':templates,'precision':precision})
    if key in _CURVE_CHECKED:
        return _copy(_CURVE_CHECKED[key])
    mb,cb,eb=(precision[k] for k in ('mode_bits','coefficient_bits','exponential_bits'))
    _require(type(mb) is int and 32<=mb<=256 and type(cb) is int and 64<=cb<=512 and
        type(eb) is int and 64<=eb<=1024,'registered complete shared-mode precision required')
    quantum=1<<mb;begin={};end={};local_error=Q(0);certificates=[]
    cp_budget=Q(1,10**10);cp_paid=Q(0)
    for template,weight in zip(templates,witness['weights']):
        _require(type(weight) is list and len(weight)==2 and all(type(v) is int for v in weight),
            'untrusted dyadic complex source-mode weight required')
        if weight==[0,0]:
            _validate_zero_template(source,template,precision)
            certificates.append({'template_digest':_digest(template),'exact_complex_weight':['0','0'],
                'weighted_complete_template_error':'0','whole_trial_term_is_exactly_zero':True,
                'source_matrix_or_action_claimed_zero':False})
            continue
        a,b=(Q(v,quantum) for v in weight);weight_norm=abs(a)+abs(b);prepared=None
        if weight_norm*4*_template_norm_bound(template,precision)<=cp_budget-cp_paid:
            proposed=_cp_endpoint_template(source,template,precision)
            if weight_norm*proposed['error']<=cp_budget-cp_paid:
                prepared=proposed;cp_paid+=weight_norm*prepared['error']
        if prepared is None:
            prepared=_prepare_template(source,template,precision)
        fourier._add_rational(begin,prepared['begin'],(a,b));fourier._add_rational(end,prepared['end'],(a,b))
        payment=(abs(a)+abs(b))*prepared['error'];local_error+=payment
        certificates.append({'template_digest':prepared['certificate']['raw_template_digest'],
            'classification':prepared['certificate'].get('classification','original_curve_residual_certified'),
            'exact_complex_weight':list(map(str,(a,b))),'weighted_complete_template_error':str(payment)})
        if prepared['certificate'].get('classification')=='CP_endpoint_norm_enclosure':
            certificates[-1]['source_CP_endpoint_certificate']={**prepared['certificate'],
                'complete_complex_B0':channel._input_record({k:dipole.ComplexRadical(*v) for k,v in prepared['begin'].items()}),
                'complete_saved_complex_Qend':channel._input_record({k:dipole.ComplexRadical(*v) for k,v in prepared['end'].items()})}
    initial=_matrix(raw['complete_initial_local_factor']);centre={};rounding=Q(0)
    for point,value in initial.items():
        a,ea=full.radical_midpoint(value.real,cb);b,ebound=full.radical_midpoint(value.imag,cb)
        full._add(centre,point,a,b);rounding+=ea+ebound
    gap=fourier._difference(fourier._hermitian(begin),centre);error=Q(raw['factor_upstream_error'])+rounding+gap+local_error
    clock=reference._phase_clock_price(atomic._read_phase(raw['source_phase']),
        (Q(0),Q(raw['physical_duration_seconds'])),raw['reference_clock'],bsm._entry_norm(initial,bits=cb),cb)
    error,outward=reference._outward_error(error+Q(clock['total_trace_norm_payment']),cb)
    result={'schema':PHASE_SCHEMA+'/coimage','source_record':raw,'untrusted_shared_witness':_copy(witness),
        'shared_templates_digest':_digest(templates),'precision':precision,
        'full_local_poststate':channel._input_record({k:dipole.ComplexRadical(*v) for k,v in fourier._hermitian(end).items()}),
        'trace_norm_error':str(error),'old_factor_error_once':raw['factor_upstream_error'],
        'source_reference_clock_price':clock,'error_outward_rounding':str(outward),
        'original_template_certificates':certificates,'source_input_join_error':str(gap),
        'weighted_original_residual_and_scalar_error':str(local_error),
        'source_CP_endpoint_enclosure_payment':str(cp_paid),'source_CP_endpoint_enclosure_budget':str(cp_budget),
        'source_phase_Taylor_tail_used':False,'source_model_mean_payment':'0',
        'mode_or_graph_correctness_assumed':False,'full33_coordinates_and_outside_trial_space_priced':True,
        'shared_error_formula':'oldFactorE_once + join + sum(weight_entry_norm * original_template_whole_error) + pi',
        'complex_mode_weights_are_untrusted_curve_coefficients':True}
    _CHECKED[_digest(result)]=_copy(result);_CURVE_CHECKED[key]=_copy(result);return result


class _FactorPhaseSource:
    def __init__(self,*args,**kwargs):
        raise ValueError('factor phases are emitted by the closed programme and its checked predecessor')

    def record(self):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('sequential Fourier executed source closure changed')
        _GUARD()
        _require(type(self) is _FactorPhaseSource and set(vars(self))=={'_frame','_seal'} and
            self._seal in _PHASE_ISSUED and _digest(self._frame)==self._seal and
            self._frame['source_bindings']==_bindings(),'issued factor phase, previous state or executed source changed')
        return _copy(self._frame)

    def certify(self,pieces,*,mode_bits=60,coefficient_bits=160,exponential_bits=160):
        return _certify_phase(self,pieces,dict(mode_bits=mode_bits,coefficient_bits=coefficient_bits,exponential_bits=exponential_bits))

    def verify(self,report,templates=None):
        raw=_FactorPhaseSource.record(self)
        _require(type(report) is dict and report.get('schema')==PHASE_SCHEMA+'/coimage' and report.get('source_record')==raw,
            'the actual preceding phase certificate must belong to this same programme factor')
        key=_digest(report)
        if key not in _CHECKED:
            rebuilt=(_certify_phase(self,report['untrusted_curve'],report['precision']) if 'untrusted_curve' in report else
                _certify_shared_phase(self,report['untrusted_shared_witness'],templates,report['precision']))
            _require(rebuilt==report,
                'preceding raw phase, matrix, clock or automatic source price changed')
        else:
            _require(_CHECKED[key]==report,'cached full original-G certificate changed')
        return True


class _WriterFrameColumns:
    def __init__(self,seed,bits):
        self.original=fourier._Columns(seed,bits);tones=self.original.tensor.programme.tones;names=tuple(t.name for t in tones)
        count=len(tones);zero=(0,)*count
        if count==1:
            self.words=tuple((1,) if state.family==tones[0].line else zero for state in dipole.STATES)
            self.delta=None;self.frequency=Q(0)
        else:
            _require(count==2 and set(names)=={'pump1to1','pump2to1'},'complete original dual pump or single excitation writer required')
            self.delta=tuple(int(j==names.index('pump1to1'))-int(j==names.index('pump2to1')) for j in range(count))
            excited=tuple(int(j==names.index('pump1to1')) for j in range(count))
            self.words=tuple(excited if state.family=='D2' else self.delta if state.family=='ground' and state.f==2 else zero
                             for state in dipole.STATES)
            self.frequency=sum((n*w for n,w in zip(self.delta,self.original.frequencies)),Q(0))
            _require(self.frequency,'nonzero original pump beat frequency required for the numerical writer')
        self.cache={}

    def column(self,key):
        if key in self.cache:
            return self.cache[key]
        i,j=key;count=len(self.words[i]);answer={}
        for component in self.original.components:
            self.original.column(component,key);carrier=[0]*count
            if component!='static':
                index,sign=component;carrier[index]-=sign
            for (a,b),value in self.original.tensor.exact_columns[component,key].items():
                word=tuple(carrier[p]-self.words[i][p]+self.words[j][p]+self.words[a][p]-self.words[b][p] for p in range(count))
                fourier._add(answer.setdefault(word,{}),{(a,b):value})
        frequency=sum(((a-b)*w for a,b,w in zip(self.words[i],self.words[j],self.original.frequencies)),Q(0))
        fourier._add(answer.setdefault((0,)*count,{}),{key:dipole.ComplexRadical(0,frequency)})
        result={word:matrix for word,matrix in answer.items() if matrix}
        self.cache[key]=result;return result

    def harmonic(self,word):
        if self.delta is None:
            _require(not any(word),'the original single-line frame is not constant on a full source column')
            return 0
        n=word[0]//self.delta[0]
        _require(word==tuple(n*d for d in self.delta),'the original complete frame leaves this writer beat lattice')
        return n


def _model(programme,side,index,harmonics,iterations,bits):
    import numpy as np
    raw=FourierReferenceLocalProgrammeSource.record(programme)['reference_local_parent']
    phase=raw['source_generated_local_plans'][side][index]['source_phase']
    key=_digest({'phase':phase,'harmonics':harmonics,'iterations':iterations,'bits':bits,'closure':_bindings()})
    if key in _MODELS:
        return _MODELS[key]
    seed=fourier.FourierLocalPhaseSource(programme._parent,side=side,phase_index=index)
    frame=_WriterFrameColumns(seed,bits);space=set()
    for inventory in raw['local_factor_inventory']:
        for item in inventory:
            space.update(_matrix(item['initial_local_matrix']))
    front=set(space)
    while front:
        added=set()
        for point in sorted(front):
            for matrix in frame.column(point).values():
                added.update(matrix)
        front=added-space;space.update(front)
    coordinates=tuple(sorted(space));addresses={point:j for j,point in enumerate(coordinates)};size=len(coordinates)
    blocks={n:np.zeros((size,size),dtype=complex) for n in (-1,0,1)}
    for point in coordinates:
        for word,matrix in frame.column(point).items():
            n=frame.harmonic(word);_require(n in blocks,'original source harmonic outside the declared writer')
            for output,value in matrix.items():
                a,_=full.radical_midpoint(value.real,bits);b,_=full.radical_midpoint(value.imag,bits)
                blocks[n][addresses[output],addresses[point]]=complex(float(a),float(b))
    static,up,down=blocks[0],blocks[1],blocks[-1];zero=np.zeros_like(static);identity=np.eye(size,dtype=complex)
    if frame.delta is None:
        graph={0:identity};effective=static
    else:
        graph={n:identity if not n else zero.copy() for n in range(-harmonics,harmonics+1)}
        for _ in range(iterations):
            effective=static+up@graph.get(-1,zero)+down@graph.get(1,zero);updated={0:identity}
            for n in graph:
                if n:
                    updated[n]=(static@graph[n]-graph[n]@effective+
                        up@graph.get(n-1,zero)+down@graph.get(n+1,zero))/(1j*n*float(frame.frequency))
                    _require(np.all(np.isfinite(updated[n])),'untrusted original phase graph iteration overflowed')
            graph=updated
        effective=static+up@graph.get(-1,zero)+down@graph.get(1,zero)
    exponents,eigenvectors=np.linalg.eig(effective)
    inverse=np.linalg.solve(eigenvectors,np.linalg.inv(sum(graph.values())))
    result={'coordinates':coordinates,'addresses':addresses,'frame_words':frame.words,'beat_word':frame.delta,
        'exponents':exponents,'inverse':inverse,'harmonic_modes':{n:matrix@eigenvectors for n,matrix in graph.items()},
        'generation':{'source_generated_complete_operator_coordinates':size,'source_original_columns':len(frame.original.tensor.columns),
            'finite_harmonic_order':0 if frame.delta is None else harmonics,'finite_graph_iterations':0 if frame.delta is None else iterations,
            'shared_numeric_phase_eigensystem_dimension':size,'eigensystem_or_graph_correctness_assumed':False}}
    _MODELS[key]=result;return result


def _model_templates(model,width,mode_bits):
    quantum=1<<mode_bits;templates=[]
    for number,exponent in enumerate(model['exponents']):
        groups={}
        for n,matrix in model['harmonic_modes'].items():
            for k,(i,j) in enumerate(model['coordinates']):
                value=matrix[k,number];a=round(float(value.real)*quantum);b=round(float(value.imag)*quantum)
                if a or b:
                    beat=model['beat_word'] or (0,)*len(model['frame_words'][i])
                    word=tuple(n*d-x+y for d,x,y in zip(beat,model['frame_words'][i],model['frame_words'][j]))
                    groups.setdefault(word,[]).append([i,j,a,b])
        cap=Q(1,2)/width;real=min(round(float(exponent.real)*quantum),(cap*quantum).numerator//(cap*quantum).denominator)
        lam=[real,round(float(exponent.imag)*quantum)]
        templates.append({'duration':str(width),'modes':[{'lambda':lam,'frequency_word':list(word),'coefficients':[matrix]}
            for word,matrix in sorted(groups.items())]})
    return templates


def _weights_trial(source,model,mode_bits,bits,templates,weight_bits):
    import numpy as np
    raw=_FactorPhaseSource.record(source);initial=_matrix(raw['complete_initial_local_factor'])
    _require(set(initial)<=set(model['addresses']),'a source-issued prior curve left the shared writer coordinates; supply a raw witness instead')
    vector=np.zeros(len(model['coordinates']),dtype=complex)
    for point,value in initial.items():
        a,_=full.radical_midpoint(value.real,bits);b,_=full.radical_midpoint(value.imag,bits)
        vector[model['addresses'][point]]=complex(float(a),float(b))
    weights=model['inverse']@vector;quantum=1<<weight_bits;scale=1<<(mode_bits-weight_bits)
    return {'template_digest':_digest(templates),'weights':[[round(float(v.real)*quantum)*scale,round(float(v.imag)*quantum)*scale] for v in weights]}


def _resume_weights(source,templates,precision,weight_bits):
    import numpy as np
    raw=_FactorPhaseSource.record(source);mb=precision['mode_bits'];quantum=1<<mb
    coordinates=set();begins=[]
    for template in templates:
        _validate_zero_template(source,template,precision);begin={}
        for mode in template['modes']:
            _require(len(mode['coefficients'])==1,'saved numerical exponential phase templates required')
            matrix=fourier._coefficient(mode['coefficients'][0],quantum)
            fourier._add_rational(begin,matrix,(Q(1),Q(0)))
        begins.append(begin);coordinates.update(begin)
    initial=_matrix(raw['complete_initial_local_factor']);coordinates.update(initial)
    coordinates=tuple(sorted(coordinates));addresses={point:i for i,point in enumerate(coordinates)}
    basis=np.zeros((len(coordinates),len(templates)),dtype=complex);vector=np.zeros(len(coordinates),dtype=complex)
    for j,begin in enumerate(begins):
        for point,(a,b) in begin.items():
            basis[addresses[point],j]=complex(float(a),float(b))
    for point,value in initial.items():
        a,_=full.radical_midpoint(value.real,precision['coefficient_bits']);b,_=full.radical_midpoint(value.imag,precision['coefficient_bits'])
        vector[addresses[point]]=complex(float(a),float(b))
    weights=np.linalg.lstsq(basis,vector,rcond=None)[0];weight_quantum=1<<weight_bits;scale=1<<(mb-weight_bits)
    return {'template_digest':_digest(templates),'weights':[[round(float(v.real)*weight_quantum)*scale,round(float(v.imag)*weight_quantum)*scale] for v in weights]}


class FourierReferenceLocalProgrammeSource:
    def __init__(self,parent):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('sequential Fourier executed source closure changed')
        _GUARD()
        _require(type(parent) is reference.ReferenceLocalPhaseSource,'closed reference Ready and raw local programme required; a target rho is not input')
        raw=reference.ReferenceLocalPhaseSource.record(parent)
        self._parent=object.__new__(reference.ReferenceLocalPhaseSource)
        self._parent._frame=_copy(raw);self._parent._seal=_digest(raw)
        self._frame={'schema':SCHEMA,'reference_local_parent':raw,
            'complete_preparation_then_excitation_plan':raw['complete_preparation_then_excitation_plan'],
            'source_input':'original Ready and all source-issued Hermitian tensor factors',
            'raw_plan_is_the_supplied_source_control':True,'free_matrix_or_target_probability_input':False,
            'controller_advance':False,'source_bindings':_bindings()}
        self._seal=_digest(self._frame);_ISSUED.add(self._seal)

    def record(self):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('sequential Fourier executed source closure changed')
        _GUARD()
        _require(type(self) is FourierReferenceLocalProgrammeSource and set(vars(self))=={'_frame','_seal','_parent'} and
            self._seal in _ISSUED and _digest(self._frame)==self._seal and self._frame['source_bindings']==_bindings() and
            reference.ReferenceLocalPhaseSource.record(self._parent)==self._frame['reference_local_parent'],
            'programme source, raw control, Ready parent or callback changed')
        return _copy(self._frame)

    @classmethod
    def from_record(cls,record):
        _require(cls is FourierReferenceLocalProgrammeSource and type(record) is dict and record.get('schema')==SCHEMA,
            'closed sequential Fourier programme source record required')
        result=cls(reference.ReferenceLocalPhaseSource.from_record(record['reference_local_parent']))
        _require(result.record()==record,'same-reference complete programme lineage changed')
        return result

    def phase_source(self,side,factor_id,preceding_certificates=(),shared_phase_templates=None):
        raw,item=_item(self,side,factor_id)
        _require(type(preceding_certificates) in (list,tuple),'the actual complete checked prefix is required')
        current=_matrix(item['initial_local_matrix']);error=Q(0);prefix=[]
        for index,report in enumerate(preceding_certificates):
            source=_emit_phase(self,side,factor_id,index,current,error,prefix)
            _FactorPhaseSource.verify(source,report,None if shared_phase_templates is None else shared_phase_templates[index])
            current=_matrix(report['full_local_poststate']);error=Q(report['trace_norm_error']);prefix.append(_digest(report))
        return _emit_phase(self,side,factor_id,len(prefix),current,error,prefix)

    def generate_trials(self,*,harmonic_order=4,graph_iterations=24,mode_bits=60,coefficient_bits=160,exponential_bits=160,
                        weight_bits=48,checkpoint_directory=None,saved_phase_templates=None):
        raw=FourierReferenceLocalProgrammeSource.record(self)['reference_local_parent']
        _require(type(harmonic_order) is int and 1<=harmonic_order<=8 and type(graph_iterations) is int and 1<=graph_iterations<=64,
            'registered untrusted shared phase writer sizes required')
        _require(type(mode_bits) is int and 32<=mode_bits<=256 and type(weight_bits) is int and 16<=weight_bits<=mode_bits,
            'registered untrusted weight proposal quantization required')
        precision=dict(mode_bits=mode_bits,coefficient_bits=coefficient_bits,exponential_bits=exponential_bits);supplied=[[],[]];generation=[];all_templates=[]
        sink=None if checkpoint_directory is None else Path(checkpoint_directory)/self._seal[:16]
        if sink is not None:
            sink.mkdir(parents=True,exist_ok=True)
        for side,inventory in enumerate(raw['local_factor_inventory']):
            saved=None if saved_phase_templates is None else saved_phase_templates[side]
            if saved is None:
                models=[_model(self,side,j,harmonic_order,graph_iterations,coefficient_bits)
                    for j in range(len(raw['source_generated_local_plans'][side]))]
                generation.append([model['generation'] for model in models])
                templates=[_model_templates(model,Q(raw['source_generated_local_plans'][side][index]['source_phase']['duration_seconds'])/
                    Q(raw['working_atomic_owner']['atomic_base']['seconds_per_unit']),mode_bits) for index,model in enumerate(models)]
            else:
                _require(type(saved) is list and len(saved)==len(raw['source_generated_local_plans'][side]),
                    'saved untrusted templates must cover every original phase')
                templates=_copy(saved);models=[None]*len(templates)
                generation.append([{'saved_untrusted_templates_reused':True,'weights_are_untrusted_least_squares_proposals':True} for t in templates])
            all_templates.append(templates)
            if sink is not None:
                (sink/f'side-{side}-untrusted-phase-templates.json').write_text(json.dumps({
                    'programme_source_record':self.record(),'precision':precision,'templates':templates,
                    'generation':generation[-1]},sort_keys=True))
            for item in inventory:
                prefix=[];curves=[]
                for index,model in enumerate(models):
                    source=FourierReferenceLocalProgrammeSource.phase_source(self,side,item['factor_id'],prefix,templates)
                    curve=(_resume_weights(source,templates[index],precision,weight_bits) if model is None else
                        _weights_trial(source,model,mode_bits,coefficient_bits,templates[index],weight_bits))
                    report=_certify_shared_phase(source,curve,templates[index],precision)
                    prefix.append(report);curves.append(curve)
                    if sink is not None:
                        name=f'side-{side}-factor-{item["factor_id"][:12]}-phase-{index}.json'
                        (sink/name).write_text(json.dumps({'untrusted_witness':curve,'certificate':report},sort_keys=True))
                supplied[side].append({'factor_id':item['factor_id'],'phase_curves':curves})
        return {'schema':SCHEMA+'/untrusted-shared-phase-curves','programme_source_record':self.record(),
            'precision':precision,'side_curves':supplied,'generation':generation,'shared_phase_templates':all_templates}

    def certify(self,trials):
        record=FourierReferenceLocalProgrammeSource.record(self);raw=record['reference_local_parent']
        _require(type(trials) is dict and set(trials)=={'schema','programme_source_record','precision','side_curves','generation','shared_phase_templates'} and
            trials['schema']==SCHEMA+'/untrusted-shared-phase-curves' and trials['programme_source_record']==record and
            type(trials['side_curves']) is list and len(trials['side_curves'])==2,'complete same-source full programme witnesses required')
        endpoints=[{},{}];certificates=[[],[]];precision=trials['precision']
        _require(type(trials['shared_phase_templates']) is list and len(trials['shared_phase_templates'])==2,
            'two complete raw phase template schedules required')
        for side,inventory in enumerate(raw['local_factor_inventory']):
            _require(type(trials['shared_phase_templates'][side]) is list and
                len(trials['shared_phase_templates'][side])==len(raw['source_generated_local_plans'][side]),
                'every raw physical phase needs its own complete original mode template')
            supplied=trials['side_curves'][side]
            _require(type(supplied) is list and [x.get('factor_id') for x in supplied]==[x['factor_id'] for x in inventory],
                'every original Ready factor must keep its own complete source witness')
            for item,witness in zip(inventory,supplied):
                curves=witness.get('phase_curves')
                _require(set(witness)=={'factor_id','phase_curves'} and type(curves) is list and
                    len(curves)==len(raw['source_generated_local_plans'][side]),'all original raw phases and durations must be covered')
                prefix=[]
                for curve in curves:
                    source=FourierReferenceLocalProgrammeSource.phase_source(self,side,item['factor_id'],prefix,trials['shared_phase_templates'][side])
                    index=len(prefix)
                    report=_certify_shared_phase(source,curve,trials['shared_phase_templates'][side][index],precision)
                    prefix.append(report)
                last=prefix[-1]
                endpoints[side][item['factor_id']]={'factor_id':item['factor_id'],'local_poststate':last['full_local_poststate'],
                    'trace_norm_error':last['trace_norm_error']}
                certificates[side].append({'factor_id':item['factor_id'],'complete_phase_certificates':prefix})
        old=Q(raw['upstream_trace_norm_error']);error=old;terms=[]
        for left,right in raw['source_tensor_factor_ids']:
            a,b=endpoints[0][left],endpoints[1][right];ma,mb=_matrix(a['local_poststate']),_matrix(b['local_poststate'])
            price,na,nb=factors._tensor_price(ma,mb,Q(a['trace_norm_error']),Q(b['trace_norm_error']),precision['coefficient_bits'])
            error+=price;terms.append({'left':a,'right':b,'local_norm_upper':[str(na),str(nb)],'tensor_error':str(price)})
        matrix=factors._expand(terms)
        relative=[sum((Q(item['raw_controls']['duration_seconds']) for item in plan),Q(0)) for plan in raw['source_generated_local_plans']]
        origin=Q(raw['source_ready_physical_clock_seconds']);absolute=[origin+x for x in relative]
        return {'schema':SCHEMA+'/complete-coimage','source_record':record,'untrusted_trials':_copy(trials),
            'complete_local_factor_certificates':certificates,'tensor_terms':terms,'full_pair_endpoint':channel._input_record(matrix),
            'trace_norm_error':str(error),'old_error_once':str(old),'source_local_and_clock_tensor_error':str(error-old),
            'source_model_mean_payment':'0','source_phase_Taylor_tail_used':False,
            'source_ready_physical_clock_seconds':str(origin),'source_local_elapsed_seconds':list(map(str,relative)),
            'source_local_emission_origins_seconds':list(map(str,absolute)),
            'complete_preparation_then_excitation_plan':raw['complete_preparation_then_excitation_plan'],
            'working_atomic_owner':raw['working_atomic_owner'],'working_common_optical_source':raw['working_common_optical_source'],
            'working_aperture_source':raw['working_aperture_source'],'same_reference_clock':raw['reference_clock'],
            'whole_reference_native_time_and_PC_mother':raw['whole_reference_native_time_and_PC_mother'],
            'native_pending_poststate':raw['native_pending_poststate'],
            'tensor_error_formula':'oldReadyE_once + sum(eA*norm(Bcentre)+eB*norm(Acentre)+eA*eB)',
            'full33_pair_retained':True,'small_terms_dropped':False,'free_target_endpoint_or_probability_input':False,
            'controller_advance':False}

    def verify(self,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/complete-coimage' and
            report.get('source_record')==FourierReferenceLocalProgrammeSource.record(self),'same complete sequential source report required')
        _require(FourierReferenceLocalProgrammeSource.certify(self,report['untrusted_trials'])==report,
            'sequential source endpoint, source clock, factor, whole error or native mother changed')
        return True


def _function(value):
    value=getattr(value,'__func__',value);return id(value),id(getattr(value,'__code__',None))


def _execution():
    functions=(_require,_copy,_digest,_bindings,_matrix,_item,_emit_phase,_certify_phase,_prepare_template,_validate_zero_template,
        _cp_endpoint_template,_template_norm_bound,_certify_shared_phase,
        _model,_model_templates,_weights_trial,_resume_weights,_function,_execution,_guard,
        reference.ReferenceLocalPhaseSource.record,reference.ReferenceLocalPhaseSource.from_record,
        reference._phase_clock_price,reference._outward_error,fourier._piece,fourier._difference,
        fourier._Columns.column,fourier._Columns.action,fourier.FourierLocalPhaseSource.record,
        exact._TensorColumns.column,atomic.AtomicPhase.record,atomic.AtomicPhase.programme,atomic._read_phase,
        factors._embed,factors._tensor_price,factors._expand,channel._read_input,channel._input_record,full.radical_midpoint)
    methods=tuple(_function(v) for cls in (FourierReferenceLocalProgrammeSource,_FactorPhaseSource,_SequentialColumns,_WriterFrameColumns)
        for v in vars(cls).values() if callable(v) or isinstance(v,(classmethod,staticmethod)))
    return tuple(map(_function,functions)),methods,tuple(dipole.STATES),tuple(dipole.INDEX.items()),full.DIMENSION,SCHEMA,PHASE_SCHEMA


def _guard():
    if _execution is not _EXECUTION or _execution.__code__ is not _EXECUTION_CODE or _execution()!=_EXPECTED:
        raise ValueError('sequential Fourier executed source closure changed')
    _require(fourier._guard is fourier._GUARD and fourier._guard.__code__ is fourier._GUARD_CODE,'original Fourier source closure changed')
    fourier._GUARD()


_EXECUTION,_EXECUTION_CODE=_execution,_execution.__code__
_GUARD,_GUARD_CODE=_guard,_guard.__code__
_EXPECTED=_execution()
