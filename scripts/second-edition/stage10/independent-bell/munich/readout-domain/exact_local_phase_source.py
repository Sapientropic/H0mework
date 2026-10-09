"""Exact raw multitone local CP action with its full33 spectator retained.

The source keeps the original time-dependent Hamiltonian.  A trial curve is
checked by its polynomial residual plus the explicit remainder of each raw
unit-modulus laser phase.  Full Zeeman and all resolved natural channels are
in the generator; no midpoint Hamiltonian or mean-field model price enters.
"""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import hashlib
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import atomic_modes as modes
import munich_atomic_programme as atomic
import optical_multitone as multitone
import fluorescence_channel as channel
import fluorescence_presence as local
import joint_fluorescence_presence as joint
import bsm_retry_source as bsm


SCHEMA='stage10-exact-raw-local-phase-tensor-source/v1'
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
    paths=(Path(__file__),*(Path(m.__file__) for m in (dipole,full,modes,atomic,multitone,channel,local,joint,bsm)))
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _phase(record):
    owner=atomic.MunichAtomicProgramme.from_record(record['parent'])
    result=atomic.MunichAtomicProgramme.phase(owner,record['kind'],record['side'],record['duration_seconds'],
             tuple(atomic.Drive.from_record(d) for d in record['drives']))
    _require(atomic.AtomicPhase.record(result)==record,'original same-owner raw phase changed')
    return result


def _read_counter(record):
    return {(c,i,j):(Q(a),Q(b)) for c,i,j,a,b in record}


def _counter_record(state):
    return [[c,i,j,str(a),str(b)] for (c,i,j),(a,b) in sorted(state.items())]


def _add_scaled(target,state,factor):
    a,b=factor
    for key,(r,s) in state.items():
        channel._add(target,key,a*r-b*s,a*s+b*r)


def _power_imaginary(value,degree):
    value=value**degree
    return ((value,Q(0)),(Q(0),value),(-value,Q(0)),(Q(0),-value))[degree%4]


def _multiply(a,b):
    r,s=a;t,u=b
    return r*t-s*u,r*u+s*t


def _dyadic_state(state,bits):
    quantum=1<<bits;result={};error=Q(0)
    for key,(a,b) in state.items():
        r=Q(round(a*quantum),quantum);s=Q(round(b*quantum),quantum)
        error+=abs(a-r)+abs(b-s)
        if r or s:
            result[key]=(r,s)
    return result,error


def _integers(state,bits):
    quantum=1<<bits
    return {key:(a.numerator*(quantum//a.denominator),b.numerator*(quantum//b.denominator)) for key,(a,b) in state.items()}


def _integer_add(target,image,factor,bits):
    quantum=1<<bits;a=factor[0].numerator*(quantum//factor[0].denominator);b=factor[1].numerator*(quantum//factor[1].denominator)
    for key,(r,s) in image.items():
        before=target.get(key,(0,0));target[key]=(before[0]+a*r-b*s,before[1]+a*s+b*r)


class _TensorColumns:
    def __init__(self,source,bits):
        record=ExactLocalPhaseSource.record(source)
        phase=_phase(record['raw_phase']);programme=atomic.AtomicPhase.programme(phase)
        owner=atomic.MunichAtomicProgramme.from_record(record['raw_phase']['parent'])
        base=atomic.MunichAtomicProgramme.atomic_base(owner)
        self.side=record['side'];self.z=atomic.AtomicBase.off_diagonal_zeeman(base,self.side)
        self.programme=programme;self.duration=Q(record['source_duration']);self.bits=bits
        self.dimension,self.threshold=joint.DIMENSION,0
        self.operations={'static':None}
        for index,tone in enumerate(programme.tones):
            excitation=programme._excitation(tone)
            self.operations[index,1]=excitation
            self.operations[index,-1]=dipole.matrix_adjoint(excitation)
        self.columns,self.errors,self.exact_columns={},{},{}

    def column(self,component,key):
        _,row,column=key
        a,b=divmod(row,full.DIMENSION);c,d=divmod(column,full.DIMENSION)
        pair=(a,c) if self.side==0 else (b,d);cache=component,pair
        if cache not in self.columns:
            initial={pair:dipole.ComplexRadical(1)}
            if component=='static':
                exact=multitone._sum(self.programme.bath.atomic_action(initial),multitone._commutator(self.z,initial))
            else:
                exact=multitone._commutator(self.operations[component],initial)
            _require(not sum((v for (i,j),v in exact.items() if i==j),ZERO),'original local action fails full trace conservation')
            centre={};error=Q(0)
            for address,value in exact.items():
                r,dr=full.radical_midpoint(value.real,self.bits);s,ds=full.radical_midpoint(value.imag,self.bits)
                quantum=1<<self.bits;dyad_real=Q(round(r*quantum),quantum);dyad_imag=Q(round(s*quantum),quantum)
                if dyad_real or dyad_imag:
                    centre[address]=(dyad_real,dyad_imag)
                error+=dr+ds+abs(r-dyad_real)+abs(s-dyad_imag)
            self.columns[cache],self.errors[cache],self.exact_columns[cache]=centre,error,exact
        def address(pair):
            i,j=pair
            return ((0,joint.atom_pair_index(i,b),joint.atom_pair_index(j,d)) if self.side==0 else
                    (0,joint.atom_pair_index(a,i),joint.atom_pair_index(c,j)))
        return {address(pair):v for pair,v in self.columns[cache].items()},self.errors[cache]

    def action(self,component,state):
        result={};price=Q(0)
        for key,(a,b) in state.items():
            column,error=self.column(component,key)
            _add_scaled(result,column,(a,b));price+=(abs(a)+abs(b))*error
        result,rounding=_dyadic_state(result,self.bits)
        return result,price+rounding


def _generator_polynomial(kernel,start,width,source_duration,order,bits):
    quantum=1<<bits;static=Q(round(source_duration*quantum),quantum)
    terms=[(0,'static',(static,Q(0)),abs(source_duration-static))];phase_remainders=[]
    for index,tone in enumerate(kernel.programme.tones):
        for sign in (1,-1):
            # +1 denotes the original raising operator with exp(-i omega t).
            omega=-sign*tone.angular_frequency
            phase,error=modes.complex_exponential(0,omega*start,bits=bits) if omega*start else ((Q(1),Q(0)),Q(0))
            for degree in range(order+1):
                coefficient=_power_imaginary(omega*width,degree)
                coefficient=(coefficient[0]/factorial(degree),coefficient[1]/factorial(degree))
                value=_multiply(phase,coefficient);quantum=1<<bits
                exact=(source_duration*value[0],source_duration*value[1])
                rounded=(Q(round(exact[0]*quantum),quantum),Q(round(exact[1]*quantum),quantum))
                numerical=source_duration*error*(abs(coefficient[0])+abs(coefficient[1]))
                numerical+=abs(exact[0]-rounded[0])+abs(exact[1]-rounded[1])
                terms.append((degree,(index,sign),rounded,numerical))
            phase_remainders.append(((index,sign),source_duration*abs(omega*width)**(order+1)/factorial(order+1)))
    return terms,phase_remainders


def _piece(kernel,piece,source_start,source_duration,elapsed,mode_bits,exp_bits,phase_order):
    _require(type(piece) is dict and set(piece)=={'duration','modes'},'untrusted normalized source-time curve piece required')
    width=full.nonnegative(piece['duration']);_require(width>0,'positive exact source interval required')
    terms,tails=_generator_polynomial(kernel,source_start+source_duration*elapsed,source_duration*width,
                                      source_duration,phase_order,exp_bits)
    quantum=1<<mode_bits;work_bits=max(mode_bits,kernel.bits,exp_bits);work_quantum=1<<work_bits
    begin={};end={};residual=radical=phase_scalar=phase_tail=exp_price=Q(0);details=[]
    _require(type(piece['modes']) is list and piece['modes'],'complete source trial modes required')
    for mode in piece['modes']:
        _require(type(mode) is dict and set(mode)=={'lambda','coefficients'},'untrusted source mode required')
        exponent=mode['lambda']
        _require(type(exponent) is list and len(exponent)==2 and all(type(n) is int for n in exponent),'dyadic complex mode exponent required')
        lr,li=(Q(n,quantum) for n in exponent)
        _require(lr*width<=Q(1,2),'bounded trial mode growth required')
        _require(type(mode['coefficients']) is list and mode['coefficients'],'complete source polynomial coefficients required')
        coefficients=[channel._coefficient(record,quantum,kernel) for record in mode['coefficients']]
        polynomial=[{} for _ in range(len(coefficients)+phase_order)]
        coefficient_cost=scalar_cost=tail_cost=Q(0)
        for degree,state in enumerate(coefficients):
            actions={component:kernel.action(component,state) for component in kernel.operations}
            integer_images={component:_integers(image,work_bits) for component,(image,price) in actions.items()}
            for j,component,factor,error in terms:
                image,price=actions[component]
                _integer_add(polynomial[degree+j],integer_images[component],factor,work_bits)
                coefficient_cost+=(abs(factor[0])+abs(factor[1]))*price
                scalar_cost+=error*(channel._entry_norm(image)+price)
            for component,tail in tails:
                image,price=actions[component]
                # Integrate the u^(M+1) remainder times this curve coefficient.
                tail_cost+=tail*(channel._entry_norm(image)+price)/(phase_order+degree+2)
            integer_state=_integers(state,work_bits)
            _integer_add(polynomial[degree],integer_state,(-lr,-li),work_bits)
            if degree:
                exact=-Q(degree)/width;rounded=Q(round(exact*work_quantum),work_quantum)
                _integer_add(polynomial[degree-1],integer_state,(rounded,Q(0)),work_bits)
                scalar_cost+=abs(exact-rounded)*channel._entry_norm(state)
        defect=Q(sum(abs(a)+abs(b) for matrix in polynomial for a,b in matrix.values()),work_quantum*work_quantum)
        residual+=2*width*defect;radical+=2*width*coefficient_cost
        phase_scalar+=2*width*scalar_cost;phase_tail+=2*width*tail_cost
        scalar,error=modes.complex_exponential(lr*width,li*width,bits=exp_bits)
        for key,(a,b) in coefficients[0].items():
            channel._add(begin,key,a,b)
        for matrix in coefficients:
            _add_scaled(end,matrix,scalar)
        exp_price+=sum((channel._entry_norm(c) for c in coefficients),Q(0))*error
        details.append({'polynomial_degree':len(coefficients)-1,'exact_source_phase_order':phase_order,
            'residual_entry_norm_sum':str(defect),'source_phase_remainder_integral':str(2*width*tail_cost)})
    return width,channel._hermitian(begin),channel._hermitian(end),{
        'source_polynomial_residual':residual,'source_radical_columns':radical,
        'source_phase_origin_scalar':phase_scalar,'source_unitary_phase_tail':phase_tail,'trial_endpoint_scalar':exp_price},details


class ExactLocalPhaseSource:
    def __init__(self,phase,initial_fullpair,*,upstream_error=0,interval=None):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('exact local source executed closure changed')
        _guard()
        _require(type(phase) is atomic.AtomicPhase,'closed same-owner raw AtomicPhase required; target generator is not input')
        raw=atomic.AtomicPhase.record(phase);programme=atomic.AtomicPhase.programme(phase)
        owner=atomic.MunichAtomicProgramme.from_record(raw['parent']);base=atomic.MunichAtomicProgramme.atomic_base(owner)
        initial=channel._initial(initial_fullpair,joint.DIMENSION)
        _require(initial==dipole.matrix_adjoint(initial),'complete Hermitian source input required; centre need not be PSD')
        a,b=(Q(0),programme.base.duration) if interval is None else tuple(map(full.exact,interval))
        _require(0<=a<b<=programme.base.duration,'source slice must be inside its original local phase clock')
        z=atomic.AtomicBase.off_diagonal_zeeman(base,raw['side'])
        self._frame={'schema':SCHEMA,'raw_phase':raw,'original_multitone_programme':programme.record(),
            'side':raw['side'],'source_interval':[str(a),str(b)],'source_duration':str(b-a),
            'seconds_per_source_unit':base.record()['seconds_per_unit'],
            'physical_local_interval_seconds':[str(a*Q(base.record()['seconds_per_unit'])),str(b*Q(base.record()['seconds_per_unit']))],
            'full_off_diagonal_Zeeman':channel._input_record(z),'complete_fullpair_input':channel._input_record(initial),
            'upstream_trace_norm_error':str(full.nonnegative(upstream_error)),
            'source_generator':'G(t)=original static full33 bath + full Z + every original tone commutator',
            'spectator_action':'identity on every original33 coordinate of the other side',
            'model_error':'0','mean_field_source_used':False,'source_input_positivity_certified_here':False,
            'source_bindings':_bindings(),'controller_advance':False}
        self._seal=_digest(self._frame);_ISSUED.add(self._seal)

    def record(self):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('exact local source executed closure changed')
        _guard()
        _require(type(self) is ExactLocalPhaseSource and set(vars(self))=={'_frame','_seal'} and self._seal in _ISSUED and
                 _digest(self._frame)==self._seal and self._frame['source_bindings']==_bindings(),'exact local phase/source/input/clock changed')
        return _copy(self._frame)

    @classmethod
    def from_record(cls,record):
        _require(cls is ExactLocalPhaseSource and type(record) is dict and record.get('schema')==SCHEMA,'closed exact local source record required')
        result=cls(_phase(record['raw_phase']),channel._read_input(record['complete_fullpair_input'],joint.DIMENSION),
                   upstream_error=record['upstream_trace_norm_error'],interval=record['source_interval'])
        _require(result.record()==record,'original phase/input/full-bath source identity changed')
        return result

    def generate_trial(self,*,order=32,mode_bits=160,coefficient_bits=192,exponential_bits=192):
        _require(type(order) is int and 1<=order<=64,'finite source density jet order required')
        record=ExactLocalPhaseSource.record(self);kernel=_TensorColumns(self,coefficient_bits)
        initial=channel._read_input(record['complete_fullpair_input'],joint.DIMENSION);coefficients=[{}]
        for (i,j),v in initial.items():
            a,_=full.radical_midpoint(v.real,coefficient_bits);b,_=full.radical_midpoint(v.imag,coefficient_bits)
            channel._add(coefficients[0],(0,i,j),a,b)
        terms,_=_generator_polynomial(kernel,Q(record['source_interval'][0]),kernel.duration,kernel.duration,order,exponential_bits)
        grouped={j:[] for j in range(order+1)}
        for degree,component,factor,error in terms:
            grouped[degree].append((component,factor))
        action_cache=[{component:kernel.action(component,coefficients[0])[0] for component in kernel.operations}]
        for n in range(order):
            value={}
            for j in range(n+1):
                state=coefficients[n-j]
                for component,factor in grouped[j]:
                    image=action_cache[n-j][component]
                    _add_scaled(value,image,(factor[0]/(n+1),factor[1]/(n+1)))
            quantum=1<<mode_bits
            coefficients.append({key:(Q(round(a*quantum),quantum),Q(round(b*quantum),quantum)) for key,(a,b) in value.items()
                                 if round(a*quantum) or round(b*quantum)})
            if n+1<order:
                action_cache.append({component:kernel.action(component,coefficients[-1])[0] for component in kernel.operations})
        quantum=1<<mode_bits
        return [{'duration':'1','modes':[{'lambda':[0,0],'coefficients':[
            [[c,i,j,round(a*quantum),round(b*quantum)] for (c,i,j),(a,b) in sorted(matrix.items()) if round(a*quantum) or round(b*quantum)]
            for matrix in coefficients]}]}]

    def certify(self,pieces,*,phase_order=48,mode_bits=160,coefficient_bits=192,exponential_bits=192):
        record=ExactLocalPhaseSource.record(self)
        _require(type(pieces) is list and type(phase_order) is int and 1<=phase_order<=64 and
                 type(mode_bits) is int and 32<=mode_bits<=256 and type(coefficient_bits) is int and 64<=coefficient_bits<=512 and
                 type(exponential_bits) is int and 64<=exponential_bits<=1024,'complete untrusted source curves and registered precisions required')
        kernel=_TensorColumns(self,coefficient_bits);initial=channel._read_input(record['complete_fullpair_input'],joint.DIMENSION)
        centre={};rounding=Q(0)
        for (i,j),v in initial.items():
            a,da=full.radical_midpoint(v.real,coefficient_bits);b,db=full.radical_midpoint(v.imag,coefficient_bits)
            channel._add(centre,(0,i,j),a,b);rounding+=da+db
        error=Q(record['upstream_trace_norm_error'])+rounding;elapsed=Q(0);prices=[]
        for piece in pieces:
            width,begin,end,cost,diagnostics=_piece(kernel,piece,Q(record['source_interval'][0]),kernel.duration,elapsed,
                                                   mode_bits,exponential_bits,phase_order)
            gap=channel._difference(begin,centre);error+=gap+sum(cost.values(),Q(0));elapsed+=width
            _require(elapsed<=1,'exact local trial exceeds its original physical phase slice')
            prices.append({'normalized_duration':str(width),'initial_join_error':str(gap),**{k:str(v) for k,v in cost.items()},'mode_diagnostics':diagnostics})
            centre=end
        _require(elapsed==1,'exact local trial must cover its entire original physical phase slice')
        matrix={(i,j):dipole.ComplexRadical(a,b) for (c,i,j),(a,b) in centre.items()}
        return {'schema':SCHEMA+'/complete-local-coimage','source_record':record,'untrusted_trial_pieces':_copy(pieces),
            'precision':dict(phase_order=phase_order,mode_bits=mode_bits,coefficient_bits=coefficient_bits,exponential_bits=exponential_bits),
            'full_pair_endpoint':channel._input_record(matrix),'trace_norm_error':str(error),
            'old_error_once':record['upstream_trace_norm_error'],'initial_radical_error':str(rounding),'piece_error_records':prices,
            'source_model_payment':'0','local_source_columns_checked':len(kernel.columns),
            'source_phase_remainder_inequality':'|exp(ix)-sum_(j=0)^M (ix)^j/j!| <= |x|^(M+1)/(M+1)! for real x',
            'full_33_reference_spectator_retained':True,'numerical_centre_assumed_positive':False,
            'same_original_physical_local_clock':True,'controller_advance':False}

    def verify(self,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/complete-local-coimage' and
                 report['source_record']==ExactLocalPhaseSource.record(self),'same exact raw local source report required')
        _require(ExactLocalPhaseSource.certify(self,report['untrusted_trial_pieces'],**report['precision'])==report,
                 'raw G(t), complete local quantum coimage, phase tail or inherited price changed')
        return True

    def poststate(self,report):
        ExactLocalPhaseSource.verify(self,report)
        return channel._read_input(report['full_pair_endpoint'],joint.DIMENSION),Q(report['trace_norm_error'])


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _execution():
    functions=(_require,_copy,_digest,_bindings,_phase,_read_counter,_counter_record,_add_scaled,_power_imaginary,_multiply,
        _dyadic_state,_integers,_integer_add,
        _generator_polynomial,_piece,_function,_execution,_guard,channel._canonical,channel._coefficient,channel._hermitian,
        channel._add,channel._entry_norm,channel._difference,channel._initial,channel._read_input,channel._input_record,
        full.radical_midpoint,modes.complex_exponential,atomic.AtomicPhase.record,atomic.AtomicPhase.programme,
        atomic.AtomicBase.off_diagonal_zeeman,atomic.MunichAtomicProgramme.atomic_base,
        multitone.Programme._excitation,multitone._commutator,multitone._sum,
        local.CounterGenerator.atomic_action,local.CounterGenerator._drift,local._apply_recycling,
        dipole.matrix_product,dipole.matrix_adjoint)
    methods=tuple(_function(member) for cls in (ExactLocalPhaseSource,_TensorColumns) for member in vars(cls).values()
                  if callable(member) or isinstance(member,(classmethod,staticmethod)))
    return tuple(map(_function,functions)),methods,tuple(dipole.STATES),tuple(dipole.INDEX.items()),full.DIMENSION,joint.DIMENSION,SCHEMA


def _guard():
    if _execution is not _EXECUTION or _execution.__code__ is not _EXECUTION_CODE or _execution()!=_EXPECTED:
        raise ValueError('exact local source executed closure changed')


_EXECUTION,_EXECUTION_CODE=_execution,_execution.__code__
_GUARD,_GUARD_CODE=_guard,_guard.__code__
_EXPECTED=_execution()
