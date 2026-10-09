"""Original raw tones have an exact frequency-word residual checker.

The trial is untrusted.  Source frequency shifts are exact and colliding
exponents are merged before the full-coordinate residual is priced.  No
Taylor approximation of a laser phase enters the source law.
"""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import hashlib
import json

import atomic_dipole as dipole
import atomic_full_forward as full
import atomic_modes as scalar
import fluorescence_channel as channel
import fluorescence_presence as local
import munich_atomic_programme as atomic
import exact_local_phase_source as exact
import factorized_local_phase_source as factors
import reference_local_phase_source as reference_local
import bsm_retry_source as bsm


SCHEMA='stage10-exact-frequency-word-local-CP-source/v1'
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
        (dipole,full,scalar,channel,local,atomic,exact,factors,reference_local,bsm)))
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _read_matrix(record):
    return channel._read_input(record,full.DIMENSION)


def _add(target,matrix,coefficient=1):
    for key,value in matrix.items():
        local._add(target,key,value*coefficient)


def _add_rational(target,state,factor):
    a,b=factor
    for key,(r,s) in state.items():
        full._add(target,key,a*r-b*s,a*s+b*r)


def _hermitian(state):
    answer={}
    for i,j in set(state)|{(j,i) for i,j in state}:
        a,b=state.get((i,j),(Q(0),Q(0)));c,d=state.get((j,i),(Q(0),Q(0)))
        full._add(answer,(i,j),(a+c)/2,(b-d)/2)
    return answer


def _norm(state):
    return sum((abs(a)+abs(b) for a,b in state.values()),Q(0))


def _upper_price(value,bits):
    _require(value>=0,'nonnegative source scalar price required')
    quantum=1<<bits
    return Q((value.numerator*quantum+value.denominator-1)//value.denominator,quantum)


def _difference(first,second):
    return sum((abs(first.get(k,(0,0))[0]-second.get(k,(0,0))[0])+
                abs(first.get(k,(0,0))[1]-second.get(k,(0,0))[1]) for k in set(first)|set(second)),Q(0))


def _coefficient(record,quantum):
    _require(type(record) is list,'complete full33 Fourier coefficient required')
    answer={}
    for row in record:
        _require(type(row) is list and len(row)==4 and all(type(v) is int for v in row),
                 'dyadic full33 Fourier matrix row required')
        i,j,a,b=row
        _require(0<=i<full.DIMENSION and 0<=j<full.DIMENSION and (i,j) not in answer and (a or b),
                 'canonical original full33 Fourier coefficient address required')
        answer[i,j]=(Q(a,quantum),Q(b,quantum))
    return answer


def _frequency(mode,frequencies,quantum):
    _require(type(mode) is dict and set(mode)=={'lambda','frequency_word','coefficients'},
             'untrusted lambda, source frequency word and complete coefficients required')
    exponent,word=mode['lambda'],mode['frequency_word']
    _require(type(exponent) is list and len(exponent)==2 and all(type(x) is int for x in exponent) and
             type(word) is list and len(word)==len(frequencies) and all(type(x) is int and abs(x)<=128 for x in word),
             'dyadic lambda and bounded integer word over the original source tones required')
    return Q(exponent[0],quantum),Q(exponent[1],quantum)+sum((n*w for n,w in zip(word,frequencies)),Q(0))


class _Columns:
    def __init__(self,source,bits):
        record=FourierLocalPhaseSource.record(source)
        phase=atomic._read_phase(record['source_phase'])
        initial=_read_matrix(record['complete_initial_local_factor'])
        lifted=exact.ExactLocalPhaseSource(phase,factors._embed(initial,record['side']))
        self.tensor=exact._TensorColumns(lifted,bits);self.side=record['side'];self.bits=bits
        self.frequencies=tuple(t.angular_frequency for t in self.tensor.programme.tones)
        self.components=tuple(self.tensor.operations);self.cache={}

    def column(self,component,key):
        if (component,key) in self.cache:
            return self.cache[component,key]
        i,j=key
        row=(full.DIMENSION*i+dipole.ION if self.side==0 else full.DIMENSION*dipole.ION+i)
        column=(full.DIMENSION*j+dipole.ION if self.side==0 else full.DIMENSION*dipole.ION+j)
        values,error=self.tensor.column(component,(0,row,column));answer={}
        for (counter,a,b),pair in values.items():
            ra,rb=divmod(a,full.DIMENSION);ca,cb=divmod(b,full.DIMENSION)
            _require(counter==0 and ((rb,cb)==(dipole.ION,dipole.ION) if self.side==0 else
                                     (ra,ca)==(dipole.ION,dipole.ION)),
                     'original source column changed its identity spectator')
            answer[(ra,ca) if self.side==0 else (rb,cb)]=pair
        self.cache[component,key]=answer,error
        return answer,error

    def action(self,component,state):
        answer={};error=Q(0)
        for key,pair in state.items():
            column,price=self.column(component,key)
            _add_rational(answer,column,pair);error+=(abs(pair[0])+abs(pair[1]))*price
        answer,rounding=exact._dyadic_state(answer,self.bits)
        return answer,error+rounding


def _integer_accumulate(target,state,factor,bits):
    quantum=1<<bits;a,b=factor
    for key,(r,s) in state.items():
        x=a*r-b*s;y=a*s+b*r
        _require((x*quantum*quantum).denominator==1 and (y*quantum*quantum).denominator==1,
                 'registered Fourier residual grids are not dyadic')
        old=target.get(key,(0,0));target[key]=(old[0]+int(x*quantum*quantum),old[1]+int(y*quantum*quantum))


def _piece(columns,piece,start,mode_bits,exponential_bits,*,return_complex_endpoints=False):
    _require(type(return_complex_endpoints) is bool,'explicit complex endpoint readout flag required')
    _require(type(piece) is dict and set(piece)=={'duration','modes'} and type(piece['modes']) is list and piece['modes'],
             'complete untrusted Fourier source curve piece required')
    width=full.exact(piece['duration']);_require(width>0,'positive original source-time Fourier interval required')
    quantum=1<<mode_bits;bits=max(mode_bits,columns.bits);work=1<<bits
    groups={};begin={};end={};radical=coefficient_rounding=origin_scalar=endpoint_scalar=Q(0);mode_records=[]
    source_phases={}
    for index,w in enumerate(columns.frequencies):
        for sign in (1,-1):
            angle=-sign*w*start
            phase,error=scalar.complex_exponential(0,angle,bits=exponential_bits) if angle else ((Q(1),Q(0)),Q(0))
            source_phases[index,sign]=phase,_upper_price(error,max(bits,exponential_bits))
    for mode in piece['modes']:
        lr,nu=_frequency(mode,columns.frequencies,quantum)
        _require(lr*width<=Q(1,2),'bounded untrusted Fourier mode growth required')
        _require(type(mode['coefficients']) is list and mode['coefficients'],'complete Fourier polynomial required')
        coefficients=[_coefficient(record,quantum) for record in mode['coefficients']]
        key=(lr,nu)
        for degree,state in enumerate(coefficients):
            polynomial=groups.setdefault(key,{})
            target=polynomial.setdefault(degree,{})
            rounded=(Q(round(lr*work),work),Q(round(nu*work),work))
            _integer_accumulate(target,state,rounded,bits)
            coefficient_rounding+=(abs(lr-rounded[0])+abs(nu-rounded[1]))*_norm(state)
            if degree:
                exact_derivative=Q(degree)/width;dyadic=Q(round(exact_derivative*work),work)
                _integer_accumulate(polynomial.setdefault(degree-1,{}),state,(dyadic,Q(0)),bits)
                coefficient_rounding+=abs(exact_derivative-dyadic)*_norm(state)
            image,error=columns.action('static',state)
            _integer_accumulate(target,image,(Q(-1),Q(0)),bits);radical+=error
            for index,w in enumerate(columns.frequencies):
                for sign in (1,-1):
                    shifted=(lr,nu-sign*w);phase,phase_error=source_phases[index,sign]
                    rounded_phase=(Q(round(phase[0]*work),work),Q(round(phase[1]*work),work))
                    image,error=columns.action((index,sign),state)
                    _integer_accumulate(groups.setdefault(shifted,{}).setdefault(degree,{}),image,
                                        (-rounded_phase[0],-rounded_phase[1]),bits)
                    radical+=(abs(rounded_phase[0])+abs(rounded_phase[1]))*error
                    origin_scalar+=(phase_error+abs(phase[0]-rounded_phase[0])+abs(phase[1]-rounded_phase[1]))*(_norm(image)+error)
        for address,pair in coefficients[0].items():
            full._add(begin,address,*pair)
        value,error=scalar.complex_exponential(lr*width,nu*width,bits=exponential_bits)
        for matrix in coefficients:
            _add_rational(end,matrix,value)
        error=_upper_price(error,max(bits,exponential_bits))
        norm=sum((_norm(matrix) for matrix in coefficients),Q(0));endpoint_scalar+=norm*error
        mode_records.append({'exact_real_exponent':str(lr),'exact_imag_exponent_including_source_word':str(nu),
            'polynomial_degree':len(coefficients)-1,'coefficient_entry_norm_sum':str(norm),'endpoint_scalar_price':str(norm*error)})
    defect=Q(sum(abs(a)+abs(b) for polynomial in groups.values() for matrix in polynomial.values()
                 for a,b in matrix.values()),work*work)
    prices={'full_frequency_merged_residual':2*width*defect,'original_radical_column_price':2*width*radical,
        'dyadic_residual_coefficient_price':2*width*coefficient_rounding,
        'source_phase_origin_scalar_price':2*width*origin_scalar,'endpoint_scalar_price':endpoint_scalar}
    result=width,_hermitian(begin),_hermitian(end),prices,{
        'exact_frequency_groups':len(groups),'mode_records':mode_records,'residual_before_integration':str(defect),
        'frequency_collisions_merged_before_norm':True,'source_phase_Taylor_tail_used':False}
    return result+(begin,end) if return_complex_endpoints else result


def _multiply_pair(a,b):
    return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]


def _inverse_pair(a):
    square=a[0]*a[0]+a[1]*a[1]
    _require(square>0,'nonzero exact source exponential required for analytic integration')
    return a[0]/square,-a[1]/square


def _integrate_mode(word,coefficients,frequencies,width):
    frequency=sum((n*w for n,w in zip(word,frequencies)),Q(0));result={};zero=(0,)*len(word)
    for degree,matrix in enumerate(coefficients):
        if not frequency:
            target=result.setdefault(zero,{})
            _add_rational(target.setdefault(degree+1,{}),matrix,(width/Q(degree+1),Q(0)))
        else:
            inverse=_inverse_pair((Q(0),frequency*width));power=(Q(1),Q(0))
            for j in range(degree+1):
                power=_multiply_pair(power,inverse)
                number=width*Q((-1)**j*factorial(degree),factorial(degree-j))
                factor=(power[0]*number,power[1]*number)
                _add_rational(result.setdefault(word,{}).setdefault(degree-j,{}),matrix,factor)
                if j==degree:
                    _add_rational(result.setdefault(zero,{}).setdefault(0,{}),matrix,(-factor[0],-factor[1]))
    return result


def _picard_trial(source,order,mode_bits,coefficient_bits):
    record=FourierLocalPhaseSource.record(source);columns=_Columns(source,coefficient_bits)
    width=Q(record['source_duration']);quantum=1<<mode_bits;initial={}
    for key,value in _read_matrix(record['complete_initial_local_factor']).items():
        a,_=full.radical_midpoint(value.real,coefficient_bits);b,_=full.radical_midpoint(value.imag,coefficient_bits)
        initial[key]=(Q(round(a*quantum),quantum),Q(round(b*quantum),quantum))
    zero=(0,)*len(columns.frequencies);modes={zero:[initial]}
    for n in range(order):
        action={}
        for word,coefficients in modes.items():
            for degree,state in enumerate(coefficients):
                for component in columns.components:
                    shifted=list(word)
                    if component!='static':
                        index,sign=component;shifted[index]-=sign
                    image,_=columns.action(component,state)
                    _add_rational(action.setdefault(tuple(shifted),{}).setdefault(degree,{}),image,(Q(1),Q(0)))
        updated={zero:{0:dict(initial)}}
        for word,polynomial in action.items():
            coefficients=[polynomial.get(j,{}) for j in range(max(polynomial,default=0)+1)]
            for label,integral in _integrate_mode(word,coefficients,columns.frequencies,width).items():
                for degree,state in integral.items():
                    _add_rational(updated.setdefault(label,{}).setdefault(degree,{}),state,(Q(1),Q(0)))
        modes={}
        for word,polynomial in updated.items():
            coefficients=[]
            for degree in range(max(polynomial,default=0)+1):
                state={}
                for key,(a,b) in polynomial.get(degree,{}).items():
                    a=Q(round(a*quantum),quantum);b=Q(round(b*quantum),quantum)
                    if a or b:
                        state[key]=(a,b)
                coefficients.append(state)
            if any(coefficients):
                modes[word]=coefficients
    return [{'duration':str(width),'modes':[{'lambda':[0,0],'frequency_word':list(word),'coefficients':[
        [[i,j,round(a*quantum),round(b*quantum)] for (i,j),(a,b) in sorted(matrix.items()) if a or b]
        for matrix in coefficients]} for word,coefficients in sorted(modes.items())]}]


class _PumpFrameColumns:
    """An exact change of coordinates of every original source column."""
    def __init__(self,source,bits):
        self.original=_Columns(source,bits)
        names=tuple(t.name for t in self.original.tensor.programme.tones)
        _require(set(names)=={'pump1to1','pump2to1'} and len(names)==2,
                 'this Fourier writer requires both original D2 pump tones')
        self.delta=tuple(int(j==names.index('pump1to1'))-int(j==names.index('pump2to1')) for j in range(2))
        excited=tuple(int(j==names.index('pump1to1')) for j in range(2))
        self.words=tuple(excited if s.family=='D2' else self.delta if s.family=='ground' and s.f==2 else (0,0)
                         for s in dipole.STATES)
        self.frequency=sum((a*b for a,b in zip(self.delta,self.original.frequencies)),Q(0))
        _require(self.frequency,'distinct original pump frequencies required for this writer')
        self.cache={}

    def column(self,key):
        if key in self.cache:
            return self.cache[key]
        i,j=key;answer={}
        for component in self.original.components:
            self.original.column(component,key)
            matrix=self.original.tensor.exact_columns[component,key]
            carrier=[0,0]
            if component!='static':
                index,sign=component;carrier[index]-=sign
            for (a,b),value in matrix.items():
                word=tuple(carrier[k]-self.words[i][k]+self.words[j][k]+self.words[a][k]-self.words[b][k]
                           for k in range(2))
                _add(answer.setdefault(word,{}),{(a,b):value})
        frequency=sum((w*f for w,f in zip(self.words[i],self.original.frequencies)),Q(0))
        frequency-=sum((w*f for w,f in zip(self.words[j],self.original.frequencies)),Q(0))
        _add(answer.setdefault((0,0),{}),{key:dipole.ComplexRadical(0,frequency)})
        self.cache[key]={word:matrix for word,matrix in answer.items() if matrix}
        return self.cache[key]

    def harmonic(self,word):
        n=word[0]//self.delta[0]
        _require(word==tuple(n*k for k in self.delta),
                 'the complete transformed source has a frequency outside this one-dimensional writer lattice')
        return n


def _floquet_trial(source,harmonic_order,krylov_dimension,mode_bits,coefficient_bits):
    # The numerical eigensystem only proposes a curve; _piece checks the original G(t).
    import numpy as np
    raw=FourierLocalPhaseSource.record(source);frame=_PumpFrameColumns(source,coefficient_bits)
    initial=_read_matrix(raw['complete_initial_local_factor']);space=set(initial);front=set(initial)
    while front:
        added=set()
        for key in sorted(front):
            for matrix in frame.column(key).values():
                added.update(matrix)
        front=added-space;space.update(front)
    coordinates=tuple(sorted(space));index={key:j for j,key in enumerate(coordinates)}
    size=len(coordinates);levels=2*harmonic_order+1;dimension=levels*size
    edges={}
    for key in coordinates:
        for word,matrix in frame.column(key).items():
            harmonic=frame.harmonic(word)
            for output,value in matrix.items():
                a,_=full.radical_midpoint(value.real,coefficient_bits);b,_=full.radical_midpoint(value.imag,coefficient_bits)
                edges.setdefault(harmonic,[]).append((index[output],index[key],complex(float(a),float(b))))
    numeric={n:(np.array([x[0] for x in rows]),np.array([x[1] for x in rows]),
                np.array([x[2] for x in rows],dtype=complex)) for n,rows in edges.items()}
    frequency=float(frame.frequency)
    def action(vector):
        blocks=vector.reshape(levels,size);result=np.zeros_like(blocks)
        for level,n in enumerate(range(-harmonic_order,harmonic_order+1)):
            result[level]-=1j*n*frequency*blocks[level]
            for shift,(rows,cols,values) in numeric.items():
                incoming=level-shift
                if 0<=incoming<levels:
                    np.add.at(result[level],rows,values*blocks[incoming,cols])
        return result.reshape(-1)
    vector=np.zeros(dimension,dtype=complex)
    for key,value in initial.items():
        a,_=full.radical_midpoint(value.real,coefficient_bits);b,_=full.radical_midpoint(value.imag,coefficient_bits)
        vector[harmonic_order*size+index[key]]=complex(float(a),float(b))
    initial_norm=np.linalg.norm(vector);_require(initial_norm>0,'nonzero source-generated local factor required')
    maximum=min(krylov_dimension,dimension);basis=np.zeros((dimension,maximum+1),dtype=complex)
    hessenberg=np.zeros((maximum+1,maximum),dtype=complex);basis[:,0]=vector/initial_norm;used=maximum
    for j in range(maximum):
        image=action(basis[:,j])
        for _ in range(2):
            projections=basis[:,:j+1].conj().T@image
            hessenberg[:j+1,j]+=projections;image-=basis[:,:j+1]@projections
        norm=np.linalg.norm(image);hessenberg[j+1,j]=norm
        if norm<1e-12:
            used=j+1;break
        basis[:,j+1]=image/norm
    eigenvalues,eigenvectors=np.linalg.eig(hessenberg[:used,:used])
    starting=np.zeros(used,dtype=complex);starting[0]=initial_norm
    weights=np.linalg.solve(eigenvectors,starting);amplitudes=(basis[:,:used]@eigenvectors)*weights
    width=Q(raw['source_duration']);quantum=1<<mode_bits;modes=[]
    for number,exponent in enumerate(eigenvalues):
        groups={}
        for level,n in enumerate(range(-harmonic_order,harmonic_order+1)):
            for k,(i,j) in enumerate(coordinates):
                value=amplitudes[level*size+k,number]
                a=round(float(value.real)*quantum);b=round(float(value.imag)*quantum)
                if a or b:
                    word=tuple(n*frame.delta[p]-frame.words[i][p]+frame.words[j][p] for p in range(2))
                    groups.setdefault(word,[]).append([i,j,a,b])
        real=min(Q.from_float(float(exponent.real)),Q(1,2)/width)
        lam=[round(real*quantum),round(float(exponent.imag)*quantum)]
        for word,matrix in sorted(groups.items()):
            modes.append({'lambda':lam,'frequency_word':list(word),'coefficients':[matrix]})
    return {'untrusted_curve':[{'duration':str(width),'modes':modes}],
        'generation':{'source_generated_operator_coordinates':size,'finite_harmonic_order':harmonic_order,
          'finite_extended_operator_dimension':dimension,'untrusted_krylov_dimension':used,
          'original_full33_source_columns_generated':len(frame.original.tensor.columns),
          'dropped_coordinate_or_closedness_premise':False,'eigensystem_correctness_assumed':False,
          'full_original_Fourier_checker_required':True}}


def _graph_floquet_trial(source,harmonic_order,iterations,mode_bits,coefficient_bits):
    import numpy as np
    raw=FourierLocalPhaseSource.record(source);frame=_PumpFrameColumns(source,coefficient_bits)
    initial=_read_matrix(raw['complete_initial_local_factor']);space=set(initial);front=set(initial)
    while front:
        added=set()
        for key in sorted(front):
            for matrix in frame.column(key).values():
                added.update(matrix)
        front=added-space;space.update(front)
    coordinates=tuple(sorted(space));index={key:j for j,key in enumerate(coordinates)};size=len(coordinates)
    blocks={n:np.zeros((size,size),dtype=complex) for n in (-1,0,1)}
    for key in coordinates:
        for word,matrix in frame.column(key).items():
            n=frame.harmonic(word)
            _require(n in blocks,'this numerical central-graph writer requires the original single beat frequency')
            for output,value in matrix.items():
                a,_=full.radical_midpoint(value.real,coefficient_bits);b,_=full.radical_midpoint(value.imag,coefficient_bits)
                blocks[n][index[output],index[key]]=complex(float(a),float(b))
    static,raising,lowering=blocks[0],blocks[1],blocks[-1];frequency=float(frame.frequency)
    zero=np.zeros_like(static);identity=np.eye(size,dtype=complex)
    graph={n:identity if n==0 else zero.copy() for n in range(-harmonic_order,harmonic_order+1)}
    for _ in range(iterations):
        effective=static+raising@graph.get(-1,zero)+lowering@graph.get(1,zero)
        updated={0:identity}
        for n in graph:
            if n:
                updated[n]=(static@graph[n]-graph[n]@effective+
                    raising@graph.get(n-1,zero)+lowering@graph.get(n+1,zero))/(1j*n*frequency)
                _require(np.all(np.isfinite(updated[n])),'the untrusted source graph iteration overflowed')
        graph=updated
    effective=static+raising@graph.get(-1,zero)+lowering@graph.get(1,zero)
    vector=np.zeros(size,dtype=complex)
    for key,value in initial.items():
        a,_=full.radical_midpoint(value.real,coefficient_bits);b,_=full.radical_midpoint(value.imag,coefficient_bits)
        vector[index[key]]=complex(float(a),float(b))
    starting=np.linalg.solve(sum(graph.values()),vector)
    eigenvalues,eigenvectors=np.linalg.eig(effective);weights=np.linalg.solve(eigenvectors,starting)
    amplitudes={n:(matrix@eigenvectors)*weights for n,matrix in graph.items()}
    width=Q(raw['source_duration']);quantum=1<<mode_bits;modes=[]
    for number,exponent in enumerate(eigenvalues):
        groups={}
        for n,matrix in amplitudes.items():
            for k,(i,j) in enumerate(coordinates):
                value=matrix[k,number]
                a=round(float(value.real)*quantum);b=round(float(value.imag)*quantum)
                if a or b:
                    word=tuple(n*frame.delta[p]-frame.words[i][p]+frame.words[j][p] for p in range(2))
                    groups.setdefault(word,[]).append([i,j,a,b])
        real=min(Q.from_float(float(exponent.real)),Q(1,2)/width)
        lam=[round(real*quantum),round(float(exponent.imag)*quantum)]
        for word,matrix in sorted(groups.items()):
            modes.append({'lambda':lam,'frequency_word':list(word),'coefficients':[matrix]})
    return {'untrusted_curve':[{'duration':str(width),'modes':modes}],
        'generation':{'source_generated_operator_coordinates':size,'finite_harmonic_order':harmonic_order,
          'finite_graph_iterations':iterations,'central_numeric_eigensystem_dimension':size,
          'original_full33_source_columns_generated':len(frame.original.tensor.columns),
          'graph_convergence_or_eigensystem_correctness_assumed':False,
          'finite_graph_boundary_residual_requires_original_checker':True}}


class FourierLocalPhaseSource:
    def __init__(self,parent,*,side=0,factor_id=None,phase_index=0,physical_duration_seconds=None):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('Fourier local executed source closure changed')
        _GUARD()
        _require(type(parent) is reference_local.ReferenceLocalPhaseSource,'closed reference/local factor source required; a target rho is not input')
        original=reference_local.ReferenceLocalPhaseSource.record(parent)
        _require(type(side) is int and side in (0,1) and type(phase_index) is int and
                 0<=phase_index<len(original['source_generated_local_plans'][side]),'original local side and phase index required')
        inventory=original['local_factor_inventory'][side]
        _require(inventory,'a source-issued nonempty Ready factor inventory is required')
        if factor_id is None:
            def neutral_norm(item):
                matrix=_read_matrix(item['initial_local_matrix'])
                return bsm._entry_norm({key:v for key,v in matrix.items() if dipole.ION not in key},bits=160)
            chosen=max(inventory,key=neutral_norm)
        else:
            chosen=next((item for item in inventory if item['factor_id']==factor_id),None)
            _require(chosen is not None,'factor identifier is outside this source-generated inventory')
        owner=atomic.MunichAtomicProgramme.from_record(original['working_atomic_owner'])
        controls=original['source_generated_local_plans'][side][phase_index]['raw_controls']
        duration=Q(controls['duration_seconds']) if physical_duration_seconds is None else full.exact(physical_duration_seconds)
        phase=atomic.MunichAtomicProgramme.phase(owner,controls['kind'],side,duration,
            tuple(atomic.Drive.from_record(d) for d in controls['drives']))
        program=atomic.AtomicPhase.programme(phase)
        self._frame={'schema':SCHEMA,'reference_local_parent_record':original,'side':side,'factor_id':chosen['factor_id'],
            'phase_index':phase_index,
            'complete_initial_local_factor':chosen['initial_local_matrix'],'source_phase':atomic.AtomicPhase.record(phase),
            'physical_duration_seconds':str(duration),'source_duration':str(program.base.duration),
            'source_angular_frequencies':[str(t.angular_frequency) for t in program.tones],
            'raw_original_tones':[t.record() for t in program.tones],
            'reference_clock':original['reference_clock'],'factor_upstream_error':'0',
            'mother_global_error_not_paid_per_factor':original['upstream_trace_norm_error'],
            'working_atomic_owner':original['working_atomic_owner'],'working_common_optical_source':original['working_common_optical_source'],
            'working_aperture_source':original['working_aperture_source'],
            'source_input':'exact Hermitian term of the original source-generated Ready centre; mother error is paid once after tensor assembly',
            'physical_duration_override_is_raw_control':physical_duration_seconds is not None,
            'target_matrix_or_F0_population_supplied':False,'controller_advance':False,'source_bindings':_bindings()}
        self._seal=_digest(self._frame);_ISSUED.add(self._seal)

    def record(self):
        if _guard is not _GUARD or _guard.__code__ is not _GUARD_CODE:
            raise ValueError('Fourier local executed source closure changed')
        _GUARD()
        _require(type(self) is FourierLocalPhaseSource and set(vars(self))=={'_frame','_seal'} and
                 self._seal in _ISSUED and _digest(self._frame)==self._seal and self._frame['source_bindings']==_bindings(),
                 'Fourier original phase, factor, reference clock or callback changed')
        return _copy(self._frame)

    @classmethod
    def from_record(cls,record):
        _require(cls is FourierLocalPhaseSource and type(record) is dict and record.get('schema')==SCHEMA,
                 'closed Fourier raw local source record required')
        parent=reference_local.ReferenceLocalPhaseSource.from_record(record['reference_local_parent_record'])
        result=cls(parent,side=record['side'],factor_id=record['factor_id'],phase_index=record['phase_index'],
            physical_duration_seconds=record['physical_duration_seconds'] if record['physical_duration_override_is_raw_control'] else None)
        _require(result.record()==record,'original source frequency/factor/time lineage changed')
        return result

    def certify(self,pieces,*,mode_bits=160,coefficient_bits=192,exponential_bits=192):
        record=FourierLocalPhaseSource.record(self)
        _require(type(pieces) is list and type(mode_bits) is int and 32<=mode_bits<=256 and
                 type(coefficient_bits) is int and 64<=coefficient_bits<=512 and type(exponential_bits) is int and 64<=exponential_bits<=1024,
                 'untrusted whole Fourier curve and registered precisions required')
        columns=_Columns(self,coefficient_bits);initial=_read_matrix(record['complete_initial_local_factor'])
        centre={};rounding=Q(0)
        for address,value in initial.items():
            a,ea=full.radical_midpoint(value.real,coefficient_bits);b,eb=full.radical_midpoint(value.imag,coefficient_bits)
            full._add(centre,address,a,b);rounding+=ea+eb
        elapsed=Q(0);old=Q(record['factor_upstream_error']);error=old+rounding;prices=[]
        for piece in pieces:
            width,begin,end,cost,diagnostics=_piece(columns,piece,elapsed,mode_bits,exponential_bits)
            gap=_difference(begin,centre);error+=gap+sum(cost.values(),Q(0));elapsed+=width
            _require(elapsed<=Q(record['source_duration']),'Fourier curve exceeds the original physical phase')
            prices.append({'source_duration':str(width),'join_error':str(gap),**{k:str(v) for k,v in cost.items()},**diagnostics})
            centre=end
        _require(elapsed==Q(record['source_duration']),'Fourier curve must cover the entire raw physical phase')
        phase=atomic._read_phase(record['source_phase']);norm=bsm._entry_norm(initial,bits=coefficient_bits)
        pi_price=reference_local._phase_clock_price(phase,(Q(0),Q(record['physical_duration_seconds'])),
            record['reference_clock'],norm,coefficient_bits)
        error,outward=reference_local._outward_error(error+Q(pi_price['total_trace_norm_payment']),coefficient_bits)
        matrix={key:dipole.ComplexRadical(*pair) for key,pair in centre.items()}
        return {'schema':SCHEMA+'/complete-Fourier-local-coimage','source_record':record,'untrusted_curve':_copy(pieces),
            'precision':dict(mode_bits=mode_bits,coefficient_bits=coefficient_bits,exponential_bits=exponential_bits),
            'full_local_poststate':channel._input_record(matrix),'trace_norm_error':str(error),'old_factor_error_once':str(old),
            'source_reference_clock_price':pi_price,'error_outward_rounding':str(outward),'piece_error_records':prices,
            'source_local_component_columns_checked':len(columns.tensor.columns),
            'mother_global_error_not_paid_per_factor':record['mother_global_error_not_paid_per_factor'],
            'source_phase_Taylor_tail_used':False,'mode_correctness_assumed':False,
            'full33_coordinates_and_source_outside_trial_space_priced':True,
            'Hermitian_projection_of_complete_trial_used':True,'controller_advance':False}

    def generate_picard_trial(self,*,order=6,mode_bits=160,coefficient_bits=192):
        _require(type(order) is int and 1<=order<=16 and type(mode_bits) is int and 32<=mode_bits<=256,
                 'bounded source analytic Fourier/Picard order and dyadic precision required')
        return _picard_trial(self,order,mode_bits,coefficient_bits)

    def generate_floquet_trial(self,*,harmonic_order=4,krylov_dimension=128,graph_iterations=24,
                               method='central_graph',mode_bits=60,coefficient_bits=160):
        _require(type(harmonic_order) is int and 0<=harmonic_order<=8 and
            type(krylov_dimension) is int and 8<=krylov_dimension<=512 and
            type(graph_iterations) is int and 1<=graph_iterations<=64 and method in ('central_graph','krylov') and
            type(mode_bits) is int and 32<=mode_bits<=256 and type(coefficient_bits) is int and 64<=coefficient_bits<=512,
            'registered untrusted finite Fourier writer sizes required')
        return (_graph_floquet_trial(self,harmonic_order,graph_iterations,mode_bits,coefficient_bits) if method=='central_graph' else
                _floquet_trial(self,harmonic_order,krylov_dimension,mode_bits,coefficient_bits))

    def verify(self,report):
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/complete-Fourier-local-coimage' and
            report.get('source_record')==FourierLocalPhaseSource.record(self),'same original Fourier source report required')
        _require(FourierLocalPhaseSource.certify(self,report['untrusted_curve'],**report['precision'])==report,
                 'source Fourier mode/action, full matrix, reference time or price changed')
        return True


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None))


def _execution():
    functions=(_require,_copy,_digest,_bindings,_read_matrix,_add,_add_rational,_hermitian,_norm,_difference,
        _coefficient,_frequency,_upper_price,_integer_accumulate,_piece,_multiply_pair,_inverse_pair,_integrate_mode,_picard_trial,_floquet_trial,_graph_floquet_trial,_function,_execution,_guard,
        reference_local.ReferenceLocalPhaseSource.record,reference_local.ReferenceLocalPhaseSource.from_record,
        reference_local._phase_clock_price,reference_local._outward_error,
        exact._TensorColumns.column,exact._TensorColumns.action,exact._dyadic_state,
        atomic.AtomicPhase.record,atomic.AtomicPhase.programme,atomic.MunichAtomicProgramme.phase,atomic._read_phase,
        channel._canonical,channel._input_record,channel._read_input,full._add,full.radical_midpoint,
        scalar.complex_exponential,bsm._entry_norm)
    methods=tuple(_function(v) for cls in (FourierLocalPhaseSource,_Columns,_PumpFrameColumns) for v in vars(cls).values()
        if callable(v) or isinstance(v,(classmethod,staticmethod)))
    return tuple(map(_function,functions)),methods,tuple(dipole.STATES),tuple(dipole.INDEX.items()),full.DIMENSION,dipole.ION,SCHEMA


def _guard():
    if _execution is not _EXECUTION or _execution.__code__ is not _EXECUTION_CODE or _execution()!=_EXPECTED:
        raise ValueError('Fourier local executed source closure changed')
    _require(reference_local._guard is reference_local._GUARD and reference_local._guard.__code__ is reference_local._GUARD_CODE,
             'Fourier inherited source closure changed')
    reference_local._GUARD()


_EXECUTION,_EXECUTION_CODE=_execution,_execution.__code__
_GUARD,_GUARD_CODE=_guard,_guard.__code__
_EXPECTED=_execution()
