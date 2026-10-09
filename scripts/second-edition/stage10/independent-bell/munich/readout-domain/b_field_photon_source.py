"""Full static Zeeman matter and retained retarded photon coordinates.

No-jump operator curves start at source projectors and are checked against
K=-iH-R/2.  The field reads U_ground(tau-t) L U_excited(t), so a photon
already emitted into an arm survives an atom-only ground-state shadow.
"""
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
import common_optical_readout as optical
import retarded_receipt_source as receipt
import bsm_retry_source as bsm

SCHEMA='stage10-full-Zeeman-retarded-photon-source/v1'
LEG_SCHEMA=SCHEMA+'/no-jump-leg'
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
    paths=(Path(__file__),*(Path(module.__file__) for module in
        (dipole,full,modes,channel,local,joint,atomic,optical,receipt,bsm)))
    return {path.name:hashlib.sha256(path.read_bytes()).hexdigest() for path in paths}


def _closed(value):
    for cls in type(value).__mro__:
        for name,member in vars(cls).items():
            if callable(member) or isinstance(member,(classmethod,staticmethod,property)):
                _require(name not in vars(value),'source operations cannot be instance callbacks')


def _add(matrix,other,factor=1):
    for key,value in other.items():
        local._add(matrix,key,value*factor)


def _projector(sector):
    _require(sector in ('all','ground','excited'),'original full, ground or excited source sector required')
    return {(i,i):dipole.ComplexRadical(1) for i,s in enumerate(dipole.STATES)
        if sector=='all' or (sector=='ground' and s.family=='ground') or
           (sector=='excited' and s.family in ('D1','D2'))}


def _source(owner,side):
    _closed(owner)
    _require(type(owner) is atomic.MunichAtomicProgramme and type(side) is int and side in (0,1),
             'closed common atomic owner and one original leg required')
    base=atomic.MunichAtomicProgramme.atomic_base(owner)
    unit=Q(atomic.AtomicBase.record(base)['seconds_per_unit'])
    segment=atomic.AtomicBase.segment(base,side,1)
    h=dipole.hamiltonian(segment.fields_r,segment.fields_c,segment.r,segment.c,
        segment.detunings,convention=segment.field_convention)
    _add(h,atomic.AtomicBase.off_diagonal_zeeman(base,side))
    h={key:value*(1/unit) for key,value in h.items()}
    _require(h==dipole.matrix_adjoint(h) and not any(dipole.ION in key for key in h),
             'the complete source Hamiltonian must be Hermitian and retain its dark ion')
    _require(all(dipole.STATES[i].family==dipole.STATES[j].family and
                 dipole.STATES[i].m==dipole.STATES[j].m for i,j in h),
             'this static source must preserve its original family and magnetic blocks')
    physical=dipole.natural_jumps(segment.radiation_regime,dict.fromkeys(full.WIDTHS,1))
    loss={};jumps=[]
    for jump in physical:
        operator=local._matrix(jump.matrix)
        _require(all(dipole.STATES[i].family=='ground' and dipole.STATES[j].family in ('D1','D2')
                     for i,j in operator),'one original excited-to-ground natural photon required')
        rate=segment.gammas[jump.label[:2]]/unit
        _add(loss,dipole.matrix_product(dipole.matrix_adjoint(operator),operator),rate)
        group=jump.label[:3]+jump.label[4:]
        jumps.append({'group':list(group),'q':jump.label[3],'original_jump_label':list(jump.label),
                      'normalized_natural_jump_operator':channel._input_record(operator),
                      'physical_amplitude_squared_per_second':str(rate)})
    _require(not any(i!=j or value.imag for (i,j),value in loss.items()) and
             all(not loss.get((i,i),ZERO) for i,s in enumerate(dipole.STATES) if s.family in ('ground','ion')),
             'the natural source loss must be positive diagonal and absorbing on ground and ion')
    expected={(i,i):dipole.ComplexRadical(segment.gammas[s.family,s.f]/unit)
              for i,s in enumerate(dipole.STATES) if s.family in ('D1','D2')}
    _require(loss==expected,'the complete angular bath must reproduce every original natural width once')
    k={key:value*dipole.ComplexRadical(0,-1) for key,value in h.items()}
    _add(k,loss,Q(-1,2))
    identity={};_add(identity,k);_add(identity,dipole.matrix_adjoint(k));_add(identity,loss)
    _require(not identity,'K+K*+sum L*L must vanish on all33 coordinates')
    # A scalar on each source-invariant block commutes with both H and R.
    # Removing it changes representation only; its phase is restored below.
    blocks={}
    for i,s in enumerate(dipole.STATES):
        blocks.setdefault((s.family,s.m),[]).append(i)
    frame={}
    for addresses in blocks.values():
        reference,_=full.radical_midpoint(h.get((addresses[0],addresses[0]),ZERO).real,160)
        for i in addresses:
            frame[i]=reference
    _require(all(frame[i]==frame[j] for i,j in h),'source scalar frame must commute with full Zeeman')
    rotating=dict(k)
    _add(rotating,{(i,i):dipole.ComplexRadical(0,value) for i,value in frame.items() if value})
    return {'raw_segment':segment.record(),'full_H_per_second':channel._input_record(h),
        'full_R_per_second':channel._input_record(loss),'full_K_per_second':channel._input_record(k),
        'rotating_K_per_second':channel._input_record(rotating),
        'source_block_phase_frequencies':[[i,str(value)] for i,value in sorted(frame.items())],
        'source_invariant_blocks':list(blocks.values()),'original_physical_natural_jumps':jumps,
        'source_loss_identity':'K+K*+sum L*L=0',
        'field_completeness_identity':'d(U*U)/dt=-sum (L U)*(L U); absorbing ground makes zero plus one photon a TP field dilation',
        'full_non_diagonal_Zeeman_retained':True,'initial_emission_occupation_conditioned':False}


def _matrix(record):
    return receipt._matrix(record,full.DIMENSION)


def _pairs(matrix,bits):
    centre,uncertainty=full._midpoint_matrix(matrix,bits)
    return centre,full._operator_bound(uncertainty)


def _product(a,b):
    r,s=a;t,u=b
    return r*t-s*u,r*u+s*t


def _left(operator,matrix):
    rows={};result={}
    for (i,j),value in matrix.items():
        rows.setdefault(i,[]).append((j,value))
    for (i,j),value in operator.items():
        for column,other in rows.get(j,()):
            r,s=_product(value,other);full._add(result,(i,column),r,s)
    return result


def _scaled_add(matrix,other,factor):
    for key,(r,s) in other.items():
        full._add(matrix,key,factor*r,factor*s)


def _quantize(matrix,bits):
    q=1<<bits
    return {key:(Q(round(a*q),q),Q(round(b*q),q)) for key,(a,b) in matrix.items()
            if round(a*q) or round(b*q)}


def _entries(matrix,bits):
    quantum=1<<bits
    return [[i,j,int(a*quantum),int(b*quantum)] for (i,j),(a,b) in sorted(matrix.items())]


def _read_entries(entries,bits):
    _require(type(entries) is list,'complete untrusted linear operator coefficients required')
    result={};q=1<<bits
    for entry in entries:
        _require(type(entry) is list and len(entry)==4 and all(type(v) is int for v in entry),
                 'registered dyadic operator coordinate required')
        i,j,a,b=entry
        _require(0<=i<full.DIMENSION and 0<=j<full.DIMENSION and (i,j) not in result and (a or b),
                 'unique original33 operator coordinate required')
        result[i,j]=Q(a,q),Q(b,q)
    return result


def _norm(matrix):
    return full._operator_bound({key:abs(a)+abs(b) for key,(a,b) in matrix.items()})


def _difference(a,b):
    result=dict(a);_scaled_add(result,b,-1)
    return _norm(result)


def _price_upper(value,bits):
    value=full.nonnegative(value);quantum=1<<bits
    scaled=value*quantum
    return Q(-(-scaled.numerator//scaled.denominator),quantum)


def _restore(matrix,frame,time,bits):
    phases={};result={};errors={}
    for i,value in frame.items():
        if value not in phases:
            phases[value]=modes.complex_exponential(0,-value*time,bits=bits) if value*time else ((Q(1),Q(0)),Q(0))
        phase,error=phases[value];errors[i]=error
        for (row,column),entry in matrix.items():
            if row==i:
                r,s=_product(phase,entry);full._add(result,(row,column),r,s)
    return result,max(errors.values(),default=Q(0))*_norm(matrix)


def _mode_piece(piece,operator,delta,current,mode_bits,phase_bits):
    _require(type(piece) is dict and set(piece)=={'duration_seconds','modes'} and
             type(piece['modes']) is list and piece['modes'],
             'finite untrusted exponential-polynomial operator modes required')
    width=full.nonnegative(piece['duration_seconds']);_require(width>0,'positive source mode interval required')
    initial={};endpoint={};residual=Q(0);rounding=Q(0);exponential=Q(0);records=[]
    for mode in piece['modes']:
        _require(type(mode) is dict and set(mode)=={'lambda_per_second','coefficients'} and
                 type(mode['lambda_per_second']) is list and len(mode['lambda_per_second'])==2 and
                 type(mode['coefficients']) is list and 1<=len(mode['coefficients'])<=65,
                 'untrusted complex exponent and full33 polynomial coefficients required')
        lr,li=map(full.exact,mode['lambda_per_second'])
        _require(lr*width<=Q(1,2),'mode growth exceeds its registered complete clock bound')
        growth=Q(1) if lr<=0 else Q(2)
        coefficients=[_read_entries(c,mode_bits) for c in mode['coefficients']]
        _scaled_add(initial,coefficients[0],1)
        polynomial={};local_residual=Q(0);integral=Q(0)
        for n,coefficient in enumerate(coefficients):
            derivative={key:((n+1)*a,(n+1)*b) for key,(a,b) in
                        (coefficients[n+1] if n+1<len(coefficients) else {}).items()}
            defect=dict(derivative)
            _scaled_add(defect,_left(operator,coefficient),-width)
            _scaled_add(defect,{key:_product((lr*width,li*width),value)
                               for key,value in coefficient.items()},1)
            local_residual+=_norm(defect)/Q(n+1)
            integral+=_norm(coefficient)/Q(n+1)
            _scaled_add(polynomial,coefficient,1)
        scalar,scalar_error=modes.complex_exponential(lr*width,li*width,bits=phase_bits)
        _scaled_add(endpoint,{key:_product(scalar,value) for key,value in polynomial.items()},1)
        mode_residual=_price_upper(growth*local_residual,phase_bits)
        mode_rounding=_price_upper(width*delta*growth*integral,phase_bits)
        mode_exponential=_price_upper(scalar_error*_norm(polynomial),phase_bits)
        residual+=mode_residual;rounding+=mode_rounding;exponential+=mode_exponential
        records.append({'lambda_per_second':[str(lr),str(li)],'degree':len(coefficients)-1,
            'source_residual_operator_error':str(mode_residual),'raw_coefficient_operator_error':str(mode_rounding),
            'scalar_exponential_operator_error':str(mode_exponential),'curve_norm_time_integral_upper':str(width*growth*integral),
            'maximum_mode_modulus_upper':str(growth),'prices_rounded_up_to_dyadic_bits':phase_bits})
    join=_difference(current,initial)
    return width,endpoint,join+residual+rounding+exponential,{
        'join_operator_error':str(join),'source_residual_operator_error':str(residual),
        'raw_coefficient_operator_error':str(rounding),'mode_exponential_operator_error':str(exponential),
        'complete_mode_prices':records,'exact_eigen_relation_assumed':False,
        'residual':'(n+1)M_(n+1) + delta_t*lambda*M_n - delta_t*K*M_n'}


class BFieldPhotonLeg:
    def __init__(self,owner,side):
        if _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
            raise ValueError('full-Zeeman photon source execution changed')
        _CHECK()
        raw=_source(owner,side)
        self._value={'schema':LEG_SCHEMA,'common_atomic_owner':atomic.MunichAtomicProgramme.record(owner),
            'side':side,**raw,'source_bindings':_bindings(),'controller_advance':False}
        self._owner=owner;self._seal=_digest(self._value);_ISSUED.add(self._seal)

    def record(self):
        if _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
            raise ValueError('full-Zeeman photon source execution changed')
        _CHECK();_closed(self)
        _require(type(self) is BFieldPhotonLeg and set(vars(self))=={'_owner','_value','_seal'} and
                 self._seal in _ISSUED and _digest(self._value)==self._seal and self._value['source_bindings']==_bindings() and
                 atomic.MunichAtomicProgramme.record(self._owner)==self._value['common_atomic_owner'],
                 'full Zeeman photon leg source changed')
        return _copy(self._value)

    @classmethod
    def from_record(cls,record):
        _require(cls is BFieldPhotonLeg and type(record) is dict and record.get('schema')==LEG_SCHEMA,
                 'closed full-Zeeman photon leg record required')
        result=cls(atomic.MunichAtomicProgramme.from_record(record['common_atomic_owner']),record['side'])
        _require(BFieldPhotonLeg.record(result)==record,'full H, loss, natural bath or phase frame changed')
        return result

    def generate_trial(self,duration_seconds,*,sector='all',cuts_seconds=None,order=24,mode_bits=160,coefficient_bits=192):
        raw=BFieldPhotonLeg.record(self);duration=full.nonnegative(duration_seconds)
        _require(type(order) is int and 1<=order<=64 and type(mode_bits) is int and 64<=mode_bits<=1024 and
                 type(coefficient_bits) is int and 64<=coefficient_bits<=1024,'registered source operator jet precision required')
        operator,_=_pairs(_matrix(raw['rotating_K_per_second']),coefficient_bits)
        current,_=_pairs(_projector(sector),mode_bits)
        if cuts_seconds is None:
            count=1
            while _norm(operator)*duration/count>Q(1,2):
                count*=2
            cuts=tuple(duration*i/count for i in range(count+1)) if duration else (Q(0),)
        else:
            cuts=tuple(map(full.nonnegative,cuts_seconds))
        _require(cuts[0]==0 and cuts[-1]==duration and all(a<b for a,b in zip(cuts,cuts[1:])),
                 'source slices must cover the complete physical no-jump clock')
        pieces=[]
        for start,stop in zip(cuts,cuts[1:]):
            width=stop-start;term=_quantize(current,mode_bits);coefficients=[]
            for degree in range(order+1):
                coefficients.append(_entries(term,mode_bits))
                term=_quantize({key:(width*a/(degree+1),width*b/(degree+1))
                                for key,(a,b) in _left(operator,term).items()},mode_bits)
            endpoint={}
            for coefficient in coefficients:
                _scaled_add(endpoint,_read_entries(coefficient,mode_bits),1)
            pieces.append({'duration_seconds':str(width),'coefficients':coefficients});current=endpoint
        return {'schema':LEG_SCHEMA+'/untrusted-operator-curve','source_record':raw,'sector':sector,
                'duration_seconds':str(duration),'mode_bits':mode_bits,'pieces':pieces}

    def generate_modes_trial(self,duration_seconds,*,sector='all',mode_bits=160,coefficient_bits=192):
        """Source block eigensolves propose curves; they establish no claim."""
        import numpy as np
        raw=BFieldPhotonLeg.record(self);duration=full.nonnegative(duration_seconds)
        _require(type(mode_bits) is int and 64<=mode_bits<=1024 and type(coefficient_bits) is int and
                 64<=coefficient_bits<=1024,'registered untrusted mode precision required')
        projector=_projector(sector)
        operator,_=_pairs(_matrix(raw['rotating_K_per_second']),coefficient_bits)
        if not duration:
            return {'schema':LEG_SCHEMA+'/untrusted-operator-curve','source_record':raw,'sector':sector,
                    'duration_seconds':'0','mode_bits':mode_bits,'pieces':[]}
        quantum=1<<mode_bits;proposals=[]
        for block in raw['source_invariant_blocks']:
            addresses=[i for i in block if (i,i) in projector]
            if not addresses:
                continue
            _require(len(addresses)==len(block) and len(block)<=4,
                     'the original sector must contain complete source blocks of at most four states')
            matrix=np.array([[complex(float(operator.get((i,j),(0,0))[0]),float(operator.get((i,j),(0,0))[1]))
                              for j in block] for i in block],dtype=np.complex128)
            values,vectors=np.linalg.eig(matrix);inverse=np.linalg.inv(vectors)
            for k,value in enumerate(values):
                coefficient=np.outer(vectors[:,k],inverse[k,:])
                _require(bool(np.isfinite(value)) and bool(np.all(np.isfinite(coefficient))),
                         'the untrusted source eigensolve did not produce finite modes')
                exponent=[str(Q(round(Q(float(component))*quantum),quantum)) for component in (value.real,value.imag)]
                entries=[]
                for a,i in enumerate(block):
                    for b,j in enumerate(block):
                        z=coefficient[a,b];r,s=round(Q(float(z.real))*quantum),round(Q(float(z.imag))*quantum)
                        if r or s:
                            entries.append([i,j,r,s])
                proposals.append({'lambda_per_second':exponent,'coefficients':[entries]})
        return {'schema':LEG_SCHEMA+'/untrusted-operator-curve','source_record':raw,'sector':sector,
                'duration_seconds':str(duration),'mode_bits':mode_bits,
                'pieces':[{'duration_seconds':str(duration),'modes':proposals}]}

    def certify(self,trial,*,coefficient_bits=192,phase_bits=160):
        raw=BFieldPhotonLeg.record(self)
        _require(type(trial) is dict and set(trial)=={'schema','source_record','sector','duration_seconds','mode_bits','pieces'} and
                 trial['schema']==LEG_SCHEMA+'/untrusted-operator-curve' and trial['source_record']==raw,
                 'untrusted complete operator curve from this original source required')
        bits=trial['mode_bits'];duration=full.nonnegative(trial['duration_seconds'])
        _require(type(bits) is int and 64<=bits<=1024 and type(coefficient_bits) is int and 64<=coefficient_bits<=1024 and
                 type(phase_bits) is int and 64<=phase_bits<=1024 and type(trial['pieces']) is list,
                 'registered full operator precision and curve pieces required')
        operator,delta=_pairs(_matrix(raw['rotating_K_per_second']),coefficient_bits)
        current,_=_pairs(_projector(trial['sector']),bits);error=Q(0);elapsed=Q(0);prices=[];exponential_modes=False
        for piece in trial['pieces']:
            if type(piece) is dict and set(piece)=={'duration_seconds','modes'}:
                exponential_modes=True
                width,endpoint,price,record=_mode_piece(piece,operator,delta,current,bits,phase_bits)
                prices.append({'source_start_seconds':str(elapsed),'duration_seconds':str(width),**record})
                elapsed+=width;error+=price;current=endpoint
                continue
            _require(type(piece) is dict and set(piece)=={'duration_seconds','coefficients'} and
                     type(piece['coefficients']) is list and 1<=len(piece['coefficients'])<=65,
                     'finite untrusted polynomial operator piece required')
            width=full.nonnegative(piece['duration_seconds']);_require(width>0,'positive source slice required')
            coefficients=[_read_entries(c,bits) for c in piece['coefficients']]
            join=_difference(current,coefficients[0]);residual=Q(0);integral=Q(0);endpoint={}
            for n,coefficient in enumerate(coefficients):
                action=_left(operator,coefficient)
                derivative={key:((n+1)*a,(n+1)*b) for key,(a,b) in
                            (coefficients[n+1] if n+1<len(coefficients) else {}).items()}
                defect=dict(derivative);_scaled_add(defect,action,-width)
                residual+=_norm(defect)/Q(n+1)
                integral+=_norm(coefficient)/Q(n+1)
                _scaled_add(endpoint,coefficient,1)
            rounding=width*delta*integral
            error+=join+residual+rounding;elapsed+=width;current=endpoint
            prices.append({'source_start_seconds':str(elapsed-width),'duration_seconds':str(width),
                'join_operator_error':str(join),'source_residual_operator_error':str(residual),
                'raw_coefficient_operator_error':str(rounding),'curve_norm_time_integral_upper':str(width*integral)})
        _require(elapsed==duration,'operator witnesses must cover exactly the original physical clock')
        frame={i:Q(value) for i,value in raw['source_block_phase_frequencies']}
        physical,phase_error=_restore(current,frame,duration,phase_bits)
        if exponential_modes:
            phase_error=_price_upper(phase_error,phase_bits)
        matrix={key:dipole.ComplexRadical(*value) for key,value in physical.items()}
        return {'schema':LEG_SCHEMA+'/certified-no-jump-operator','source_record':raw,'untrusted_trial':_copy(trial),
            'duration_seconds':str(duration),'sector':trial['sector'],'full33_operator':channel._input_record(matrix),
            'operator_norm_error_upper':str(error+phase_error),'rotating_operator_error':str(error),
            'source_phase_restoration_error':str(phase_error),'coefficient_bits':coefficient_bits,'phase_bits':phase_bits,
            'complete_piece_prices':prices,'source_model_error':'0',
            'error_law':'contractive Duhamel: initial/join + integral norm(qprime-K q); source scalar block phases restored',
            'endpoint_or_eigenvector_supplied':False,'numerical_centre_assumed_contractive':False}

    def verify(self,report):
        _require(type(report) is dict and report.get('schema')==LEG_SCHEMA+'/certified-no-jump-operator',
                 'closed no-jump operator certificate required')
        _require(BFieldPhotonLeg.certify(self,report['untrusted_trial'],coefficient_bits=report['coefficient_bits'],
            phase_bits=report['phase_bits'])==report,'no-jump operator, physical source clock or residual price changed')
        return True

    def exponential_curve(self,report):
        """Read the certified analytic curve, distinct from its numeric endpoint."""
        BFieldPhotonLeg.verify(self,report)
        raw=BFieldPhotonLeg.record(self);trial=report['untrusted_trial'];bits=trial['mode_bits']
        frame={i:Q(value) for i,value in raw['source_block_phase_frequencies']}
        pieces=[];elapsed=Q(0);previous_endpoint_error=Q(0)
        for piece,price in zip(trial['pieces'],report['complete_piece_prices']):
            width=Q(piece['duration_seconds'])
            proposals=(piece['modes'] if 'modes' in piece else
                       [{'lambda_per_second':['0','0'],'coefficients':piece['coefficients']}])
            terms=[]
            for mode in proposals:
                lr,li=map(Q,mode['lambda_per_second']);coefficients=mode['coefficients']
                rows={entry[0] for coefficient in coefficients for entry in coefficient}
                frequencies=sorted({frame[i] for i in rows})
                for frequency in frequencies:
                    filtered=[[entry for entry in coefficient if frame[entry[0]]==frequency]
                              for coefficient in coefficients]
                    terms.append({'lambda_per_second':[str(lr),str(li-frequency)],
                        'mode_origin_seconds':str(elapsed),
                        'constant_source_phase_angle_radians':str(-frequency*elapsed),
                        'normalized_polynomial_coefficients':_copy(filtered),
                        'polynomial_coordinate':'(physical_elapsed_seconds - mode_origin_seconds)/piece_duration_seconds',
                        'mode_bits':bits})
            join=Q(price['join_operator_error']);residual=Q(price['source_residual_operator_error'])
            coefficient=Q(price['raw_coefficient_operator_error'])
            uniform=previous_endpoint_error+join+residual+coefficient
            endpoint_exp=Q(price.get('mode_exponential_operator_error','0'))
            pieces.append({'source_interval_seconds':[str(elapsed),str(elapsed+width)],
                'piece_duration_seconds':str(width),'complete_physical_operator_terms':terms,
                'rotating_uniform_operator_error_upper':str(uniform),
                'physical_uniform_operator_error_upper_with_exact_block_phases':str(uniform),
                'previous_rotating_endpoint_error':str(previous_endpoint_error),
                'current_endpoint_scalar_exponential_error':str(endpoint_exp),
                'uniform_price_excludes_current_endpoint_evaluation_error':True,
                'source_block_phase_functions_are_exact_unit_modulus':True})
            previous_endpoint_error=uniform+endpoint_exp;elapsed+=width
        _require(elapsed==Q(report['duration_seconds']) and
                 previous_endpoint_error==Q(report['rotating_operator_error']),
                 'uniform source curve and endpoint scalar prices must telescope to the certified record')
        return {'schema':LEG_SCHEMA+'/certified-analytic-exponential-curve','source_record':raw,
            'sector':trial['sector'],'duration_seconds':report['duration_seconds'],'pieces':pieces,
            'source_curve_not_inferred_from_endpoint':True,'exact_eigen_relation_assumed':False,
            'source_phase_model_error':'0',
            'evaluation_rule':'sum exp(constant_source_phase_angle*i) * exp(lambda*(t-origin)) * polynomial((t-origin)/width)',
            'numeric_phase_and_mode_evaluation_prices_require_separate_payment':True}


def _word(source,word,observation):
    _require(type(word) is list and len(word)<=2,'original zero, one or two photon coordinates required')
    raw=BFieldPhotonSource.record(source);time=full.nonnegative(observation)
    _require(time>=max(map(Q,raw['emission_origin_seconds'])),'observation precedes an atomic source endpoint')
    groups={tuple(jump['group']) for leg in raw['physical_legs'] for jump in leg['original_physical_natural_jumps']}
    for entry in word:
        _require(type(entry) is dict and set(entry)=={'group','mode','arrival_seconds'} and tuple(entry['group']) in groups,
                 'original resolved natural field coordinate required')
        mode=entry['mode']
        _require(type(mode) is list and len(mode)==2 and mode[0] in ('port','loss') and type(mode[1]) is int and
                 0<=mode[1]<(4 if mode[0]=='port' else 6),'original four-port or six-mode loss coordinate required')
        full.nonnegative(entry['arrival_seconds'])
    return raw,time


def _requests(source,words,observation):
    raw,time=_word(source,[],observation);requests=set()
    for word in words:
        _word(source,word,time)
        if len(word)<2:
            for side in (0,1):
                requests.add((side,'all',time-Q(raw['emission_origin_seconds'][side])))
        for entry in word:
            for side in (0,1):
                arrival=Q(entry['arrival_seconds']);flight=Q(raw['flight_seconds'][side])
                arrival_origin=Q(raw['source_arrival_origins_seconds'][side])
                emission=arrival-flight
                if arrival_origin<=arrival<=time+flight:
                    requests.add((side,'excited',arrival-arrival_origin))
                    requests.add((side,'ground',time-emission))
    return sorted(requests)


def _request_key(request):
    side,sector,duration=request
    return channel._canonical([side,sector,str(duration)])


def _certificates(source,words,observation,trials,bits):
    requests=_requests(source,words,observation)
    _require(type(trials) is dict and set(trials)=={_request_key(r) for r in requests},
             'every and only the source-derived physical clock curve is required')
    reports={}
    for request in requests:
        side,sector,duration=request;key=_request_key(request);trial=trials[key]
        _require(trial['sector']==sector and Q(trial['duration_seconds'])==duration,
                 'no-jump witnesses belong to another source sector or physical clock')
        reports[key]=BFieldPhotonLeg.certify(source._legs[side],trial,coefficient_bits=bits,phase_bits=bits)
    return reports


def _operator(reports,side,sector,duration):
    report=reports[_request_key((side,sector,duration))]
    return _matrix(report['full33_operator']),Q(report['operator_norm_error_upper'])


def _operator_bound(matrix,bits):
    centre,error=full._midpoint_matrix(matrix,bits)
    return full._norm(centre)+full._operator_bound(error)


def _sqrt_rate(value,bits):
    value=full.nonnegative(value)
    low,high=full._sqrt(value.numerator*value.denominator,bits)
    return (low+high)/(2*value.denominator),(high-low)/(2*value.denominator)


def _emission(source,side,entry,time,reports,bits):
    raw=BFieldPhotonSource.record(source)
    arrival=Q(entry['arrival_seconds']);flight=Q(raw['flight_seconds'][side])
    arrival_origin=Q(raw['source_arrival_origins_seconds'][side]);emission=arrival-flight
    if not arrival_origin<=arrival<=time+flight:
        return {},Q(0)
    before,ea=_operator(reports,side,'excited',arrival-arrival_origin)
    after,eb=_operator(reports,side,'ground',time-emission)
    transfer=tuple(tuple(channel._complex_record(v) for v in row) for row in raw['common_optical_source']['generated_four_by_six_transfer'])
    angular={};rate=None;group=tuple(entry['group']);mode=entry['mode']
    for jump in raw['physical_legs'][side]['original_physical_natural_jumps']:
        if tuple(jump['group'])!=group:
            continue
        q=jump['q'];coefficient=(transfer[mode[1]][3*side+dipole.Q_COMPONENTS.index(q)] if mode[0]=='port' else
                               dipole.ComplexRadical(int(mode[1]==3*side+dipole.Q_COMPONENTS.index(q))))
        if coefficient:
            jump_rate=Q(jump['physical_amplitude_squared_per_second'])
            _require(rate is None or rate==jump_rate,'one source-resolved group must retain its original common width')
            rate=jump_rate
            _add(angular,_matrix(jump['normalized_natural_jump_operator']),coefficient)
    amplitude,scalar_error=_sqrt_rate(Q(0) if rate is None else rate,bits)
    operator={key:value*amplitude for key,value in angular.items() if value*amplitude}
    matrix=dipole.matrix_product(dipole.matrix_product(after,operator),before)
    norm=_operator_bound(operator,bits)
    # The true ground and excited no-jump operators are contractions.
    error=norm*(ea+eb+ea*eb)+scalar_error*_operator_bound(angular,bits)
    return matrix,error


def _amplitude(source,word,time,reports,bits):
    raw,_=_word(source,word,time)
    vacuum=[];errors=[]
    if len(word)<2:
        for side in (0,1):
            a,e=_operator(reports,side,'all',time-Q(raw['emission_origin_seconds'][side]))
            vacuum.append(a);errors.append(e)
    emissions=[tuple(_emission(source,side,entry,time,reports,bits) for side in (0,1)) for entry in word]
    if not word:
        result=receipt._tensor(*vacuum);error=errors[0]+errors[1]+errors[0]*errors[1]
    elif len(word)==1:
        (a,ea),(b,eb)=emissions[0];result={}
        receipt._add(result,receipt._tensor(a,vacuum[1]));receipt._add(result,receipt._tensor(vacuum[0],b))
        error=ea*(1+errors[1])+eb*(1+errors[0])+errors[1]*_operator_bound(a,bits)+errors[0]*_operator_bound(b,bits)
    else:
        (a,ea),(b,eb)=emissions[0];(c,ec),(d,ed)=emissions[1];result={}
        factor=dipole.ComplexRadical(dipole.sqrt_rational(Q(1,2)))
        receipt._add(result,receipt._tensor(a,d),factor);receipt._add(result,receipt._tensor(c,b),factor)
        error=ea*_operator_bound(d,bits)+ed*_operator_bound(a,bits)+ea*ed+\
              ec*_operator_bound(b,bits)+eb*_operator_bound(c,bits)+ec*eb
    return result,error


class BFieldPhotonSource:
    def __init__(self,common,*,flight_seconds,emission_origin_seconds=(0,0),gate_seconds=None):
        if _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
            raise ValueError('full-Zeeman photon source execution changed')
        _CHECK()
        _require(type(common) is optical.CommonOpticalReadout,'closed same atomic/four-port optical owner required')
        _closed(common);pack=optical.CommonOpticalReadout.record(common)
        owner=atomic.MunichAtomicProgramme.from_record(pack['common_atomic_owner'])
        flights=tuple(map(full.nonnegative,flight_seconds));origins=tuple(map(full.nonnegative,emission_origin_seconds))
        _require(len(flights)==len(origins)==2,'two raw physical source origins and flights required')
        gate=(max(origins),max(origins)+bsm.GATE_SECONDS) if gate_seconds is None else tuple(map(full.nonnegative,gate_seconds))
        _require(len(gate)==2 and max(origins)<=gate[0]<=gate[1],'one fixed gate after the source endpoints required')
        transfer=tuple(tuple(channel._complex_record(v) for v in row) for row in pack['generated_four_by_six_transfer'])
        _,_,loss=joint.passive_transfer(transfer)
        self._common=common;self._legs=tuple(BFieldPhotonLeg(owner,side) for side in (0,1))
        self._bg=receipt.PortBackgroundLaw(common)
        self._value={'schema':SCHEMA,'common_optical_source':pack,'physical_legs':[leg.record() for leg in self._legs],
            'flight_seconds':list(map(str,flights)),'emission_origin_seconds':list(map(str,origins)),
            'source_arrival_origins_seconds':[str(a+b) for a,b in zip(origins,flights)],
            'gate_seconds':list(map(str,gate)),'loss_environment_gram':[[v.serialize() for v in row] for row in loss],
            'source_BG_law':receipt.PortBackgroundLaw.record(self._bg),
            'field_trace_measure':{'ordered_coordinate_sectors':[0,1,2],
                'two_photon_wavefunction_factor':dipole.sqrt_rational(Q(1,2)).serialize(),
                'resolved_natural_group_and_arrival_time_metric':'diagonal; q is a photon coordinate, not a hidden atom label'},
            'source_leg_law':'U_ground(tau-emission) L_group,q U_excited(emission-origin)',
            'future_arrival_and_loss_coordinates_retained':True,'B0_stationarity_used':False,
            'prepared_state_or_eigenvalues_supplied':False,'source_bindings':_bindings(),'controller_advance':False}
        self._seal=_digest(self._value);_ISSUED.add(self._seal)

    def record(self):
        if _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
            raise ValueError('full-Zeeman photon source execution changed')
        _CHECK();_closed(self)
        _require(type(self) is BFieldPhotonSource and set(vars(self))=={'_common','_legs','_bg','_value','_seal'} and
            self._seal in _ISSUED and _digest(self._value)==self._seal and self._value['source_bindings']==_bindings() and
            optical.CommonOpticalReadout.record(self._common)==self._value['common_optical_source'] and
            [BFieldPhotonLeg.record(leg) for leg in self._legs]==self._value['physical_legs'] and
            receipt.PortBackgroundLaw.record(self._bg)==self._value['source_BG_law'],
            'physical Zeeman field, two flights, optical loss or source BG changed')
        return _copy(self._value)

    @classmethod
    def from_record(cls,record):
        _require(cls is BFieldPhotonSource and type(record) is dict and record.get('schema')==SCHEMA,
                 'closed full-Zeeman retained field source required')
        source=cls(optical.CommonOpticalReadout.from_record(record['common_optical_source']),
            flight_seconds=record['flight_seconds'],emission_origin_seconds=record['emission_origin_seconds'],
            gate_seconds=record['gate_seconds'])
        _require(BFieldPhotonSource.record(source)==record,'full Zeeman source identity changed')
        return source

    def generate_field_trials(self,words,observation,*,order=24,mode_bits=160,coefficient_bits=192,strategy='polynomial'):
        _require(type(words) is list,'the original field words must generate every requested clock')
        _require(strategy in ('polynomial','exponential_modes'),'explicit source polynomial or exponential-mode generator required')
        if strategy=='exponential_modes':
            return {_request_key(r):BFieldPhotonLeg.generate_modes_trial(self._legs[r[0]],r[2],sector=r[1],
                mode_bits=mode_bits,coefficient_bits=coefficient_bits) for r in _requests(self,words,observation)}
        return {_request_key(r):BFieldPhotonLeg.generate_trial(self._legs[r[0]],r[2],sector=r[1],
                order=order,mode_bits=mode_bits,coefficient_bits=coefficient_bits) for r in _requests(self,words,observation)}

    def no_emission_operator(self,side,physical_time,trial,*,bits=160):
        raw=BFieldPhotonSource.record(self);time=full.nonnegative(physical_time)
        _require(type(side) is int and side in (0,1) and time>=Q(raw['emission_origin_seconds'][side]),
                 'original source side and reached physical endpoint required')
        duration=time-Q(raw['emission_origin_seconds'][side])
        _require(trial['sector']=='all' and Q(trial['duration_seconds'])==duration,
                 'full vacuum curve must cover its own physical source clock')
        report=BFieldPhotonLeg.certify(self._legs[side],trial,coefficient_bits=bits,phase_bits=bits)
        return {'source_record':raw,'side':side,'physical_time_seconds':str(time),
            'full33_vacuum_operator':report['full33_operator'],
            'operator_norm_error_upper':report['operator_norm_error_upper'],'no_jump_certificate':report,
            'ground_and_ion_vacuum_coordinates_retained':True,'scalar_bits':bits}

    def emission_operator(self,side,group,q,arrival_time,physical_observation_time,trials,*,bits=160):
        _require(type(side) is int and side in (0,1) and type(q) is int and q in dipole.Q_COMPONENTS,
                 'original physical emitter and spherical photon coordinate required')
        entry={'group':list(group),'mode':['loss',3*side+dipole.Q_COMPONENTS.index(q)],
               'arrival_seconds':str(full.nonnegative(arrival_time))}
        raw,time=_word(self,[entry],physical_observation_time)
        reports=_certificates(self,[[entry]],time,trials,bits)
        matrix,error=_emission(self,side,entry,time,reports,bits)
        return {'source_record':raw,'side':side,'radiation_group':list(group),'q':q,
            'arrival_time_seconds':entry['arrival_seconds'],
            'source_emission_time_seconds':str(Q(entry['arrival_seconds'])-Q(raw['flight_seconds'][side])),
            'physical_observation_time_seconds':str(time),'full33_one_photon_operator':channel._input_record(matrix),
            'operator_norm_error_upper':str(error),'no_jump_certificates':reports,
            'off_diagonal_time_coordinate_retained':True,'scalar_bits':bits}

    def field_amplitude(self,word,observation,trials,*,bits=160):
        raw,time=_word(self,word,observation)
        reports=_certificates(self,[word],time,trials,bits);matrix,error=_amplitude(self,word,time,reports,bits)
        return {'schema':SCHEMA+'/field-amplitude','source_record':raw,'photon_word':_copy(word),
            'physical_observation_seconds':str(time),'full_pair_operator':channel._input_record(matrix),
            'operator_error_upper':str(error),'no_jump_certificates':reports,'untrusted_trials':_copy(trials),
            'future_arrivals_not_discarded':True,'two_Bose_assignments_retained':len(word)==2,'scalar_bits':bits}

    def field_density_column(self,row,column,bra_word,ket_word,observation,trials,*,bits=160):
        _require(type(row) is int and type(column) is int and 0<=row<joint.DIMENSION and 0<=column<joint.DIMENSION,
                 'original full33 pair matrix-unit column required')
        raw,time=_word(self,bra_word,observation);_word(self,ket_word,time)
        reports=_certificates(self,[bra_word,ket_word],time,trials,bits)
        a,ea=_amplitude(self,bra_word,time,reports,bits);b,eb=_amplitude(self,ket_word,time,reports,bits)
        matrix=dipole.matrix_product(dipole.matrix_product(a,{(row,column):dipole.ComplexRadical(1)}),dipole.matrix_adjoint(b))
        error=ea*_operator_bound(b,bits)+eb*_operator_bound(a,bits)+ea*eb
        return {'schema':SCHEMA+'/matter-field-column','source_record':raw,'matrix_unit':[row,column],
            'physical_observation_seconds':str(time),'bra_photon_word':_copy(bra_word),'ket_photon_word':_copy(ket_word),
            'complete_matter_field_kernel':channel._input_record(matrix),'trace_norm_kernel_error':str(error),
            'no_jump_certificates':reports,'untrusted_trials':_copy(trials),
            'off_diagonal_photon_time_and_number_retained':True,'scalar_bits':bits}

    def field_trace_metric(self,bra_word,ket_word):
        raw,_=_word(self,bra_word,max(map(Q,self.record()['emission_origin_seconds'])))
        _word(self,ket_word,max(map(Q,raw['emission_origin_seconds'])))
        if len(bra_word)!=len(ket_word):
            return ZERO
        loss=tuple(tuple(channel._complex_record(v) for v in row) for row in raw['loss_environment_gram'])
        value=dipole.ComplexRadical(1)
        for a,b in zip(bra_word,ket_word):
            if a['group']!=b['group'] or Q(a['arrival_seconds'])!=Q(b['arrival_seconds']) or a['mode'][0]!=b['mode'][0]:
                return ZERO
            p,q=a['mode'][1],b['mode'][1]
            value*=dipole.ComplexRadical(int(p==q)) if a['mode'][0]=='port' else loss[q][p]
        return value

    def receipt_field_column(self,row,column,bra_word,ket_word,observation,trials,*,completing_signal=None,bits=160):
        raw,time=_word(self,bra_word,observation);g0,g1=map(Q,raw['gate_seconds'])
        _require(g0<=time<=g1,'first receipt is outside the original fixed physical gate')
        def observed(word):
            return sorted((Q(e['arrival_seconds'])-g0,e['mode'][1],tuple(e['group'])) for e in word
                          if e['mode'][0]=='port' and g0<=Q(e['arrival_seconds'])<time)
        _require(observed(bra_word)==observed(ket_word),'measured past photon coordinates must match on both field legs')
        past=len(observed(bra_word))
        if completing_signal is not None:
            _require(type(completing_signal) is int and 0<=completing_signal<4,'original completing port required')
            def completed(word):
                return [e for e in word if e['mode']==['port',completing_signal] and Q(e['arrival_seconds'])==time]
            a,b=completed(bra_word),completed(ket_word)
            _require(len(a)==len(b)==1 and a[0]['group']==b[0]['group'],'same resolved completing photon required')
            past+=1
        else:
            _require(not any(e['mode'][0]=='port' and Q(e['arrival_seconds'])==time for e in [*bra_word,*ket_word]),
                     'a simultaneous signal needs its source completion event')
        path=receipt.PortBackgroundLaw.path(self._bg,[[str(t),p] for t,p,g in observed(bra_word)],time-g0,
            receipt_port=completing_signal,bits=bits)
        kernel=BFieldPhotonSource.field_density_column(self,row,column,bra_word,ket_word,time,trials,bits=bits)
        factor=receipt._measurement_factor(len(bra_word),len(ket_word),past)
        matrix={key:value*factor for key,value in receipt._matrix(kernel['complete_matter_field_kernel']).items()}
        norm=bsm._entry_norm(matrix,bits=bits);error=Q(kernel['trace_norm_kernel_error'])*bsm._entry_norm({(0,0):factor},bits=bits)
        matrices=[];price=Q(0)
        for _,value,rounding in path['receipt_weights']:
            value,rounding=Q(value),Q(rounding)
            matrices.append(channel._input_record({key:value*v for key,v in matrix.items() if value*v}))
            price+=(abs(value)+rounding)*error+rounding*norm
        return {'schema':SCHEMA+'/first-receipt-field-column','source_record':raw,'matrix_unit':[row,column],
            'physical_receipt_seconds':str(time),'bra_photon_word':_copy(bra_word),'ket_photon_word':_copy(ket_word),
            'four_pattern_matter_field_kernels':matrices,'whole_four_pattern_error':str(price),
            'source_BG_path':path,'first_receipt_is_BG_rate_density':completing_signal is None,
            'completing_signal_port':completing_signal,
            'consumed_signal_photons':past,'untrusted_trials':_copy(trials),
            'remaining_bra_field':[e for e in bra_word if not(e['mode'][0]=='port' and g0<=Q(e['arrival_seconds'])<=time)],
            'remaining_ket_field':[e for e in ket_word if not(e['mode'][0]=='port' and g0<=Q(e['arrival_seconds'])<=time)],
            'in_flight_lost_and_off_diagonal_future_field_retained':True,'scalar_bits':bits}

    def verify_field_column(self,report):
        _require(type(report) is dict and report.get('schema') in (SCHEMA+'/matter-field-column',SCHEMA+'/first-receipt-field-column'),
                 'closed full-Zeeman field column required')
        row,column=report['matrix_unit']
        if report['schema']==SCHEMA+'/matter-field-column':
            result=BFieldPhotonSource.field_density_column(self,row,column,report['bra_photon_word'],report['ket_photon_word'],
                report['physical_observation_seconds'],report['untrusted_trials'],bits=report['scalar_bits'])
        else:
            port=None
            if not report['first_receipt_is_BG_rate_density']:
                port=report['completing_signal_port']
            result=BFieldPhotonSource.receipt_field_column(self,row,column,report['bra_photon_word'],report['ket_photon_word'],
                report['physical_receipt_seconds'],report['untrusted_trials'],completing_signal=port,bits=report['scalar_bits'])
        _require(result==report,'physical field, source clock, curve or whole price changed')
        return True


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None)),repr(getattr(value,'__defaults__',None)),repr(getattr(value,'__kwdefaults__',None))


def _execution():
    helpers=(_require,_copy,_digest,_bindings,_closed,_add,_projector,_source,_matrix,_pairs,_product,_left,
        _scaled_add,_quantize,_entries,_read_entries,_norm,_difference,_price_upper,_restore,_mode_piece,_word,_requests,_request_key,
        _certificates,_operator,_operator_bound,_sqrt_rate,_emission,_amplitude,_function,_execution,_check,
        atomic.MunichAtomicProgramme.record,atomic.MunichAtomicProgramme.atomic_base,atomic.MunichAtomicProgramme.from_record,
        atomic.AtomicBase.record,atomic.AtomicBase.segment,atomic.AtomicBase.off_diagonal_zeeman,
        dipole.hamiltonian,dipole.natural_jumps,dipole.matrix_product,dipole.matrix_adjoint,
        full._midpoint_matrix,full._operator_bound,full.radical_midpoint,full._sqrt,full._norm,full._add,local._matrix,local._add,
        modes.complex_exponential,channel._canonical,channel._input_record,channel._complex_record,
        optical.CommonOpticalReadout.record,optical.CommonOpticalReadout.from_record,joint.passive_transfer,
        receipt.PortBackgroundLaw.__init__,receipt.PortBackgroundLaw.record,receipt.PortBackgroundLaw.path,
        receipt._matrix,receipt._tensor,receipt._add,receipt._measurement_factor,bsm._entry_norm)
    methods=tuple(_function(member) for cls in (BFieldPhotonLeg,BFieldPhotonSource) for member in vars(cls).values()
                  if callable(member) or isinstance(member,(classmethod,staticmethod)))
    return tuple(map(_function,helpers)),methods,tuple(dipole.STATES),tuple(dipole.INDEX.items()),dipole.ION,tuple(dipole.Q_COMPONENTS),full.DIMENSION,joint.DIMENSION,SCHEMA,LEG_SCHEMA


def _check():
    if _execution is not _EXECUTION or _execution.__code__ is not _EXECUTION_CODE or _check is not _CHECK or _check.__code__ is not _CHECK_CODE:
        raise ValueError('full-Zeeman photon source execution changed')
    if _execution()!=_EXPECTED:
        raise ValueError('full-Zeeman photon source execution changed')


_EXECUTION,_EXECUTION_CODE=_execution,_execution.__code__
_CHECK,_CHECK_CODE=_check,_check.__code__
_EXPECTED=_execution()
