"""A declared Gaussian field and its full33 two-time no-jump propagator.

The duration bounds a certified observation interval.  It neither truncates
the Gaussian nor places emitted photons at its endpoint.  Numerical modes
are witnesses checked against the source K(t); no prepared state is input.
"""
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import hashlib
import json

import b_field_photon_source as field
import reference_local_phase_source as reference
import radical_time_accumulator as integer_time

atomic, dipole, full, channel, modes = field.atomic, field.dipole, field.full, field.channel, field.modes
SCHEMA='stage10-source-Gaussian-atomic-pulse/v1'
_ISSUED=set()
_REPORTS=set()


def _require(condition,message):
    if not condition:
        raise ValueError(message)


def _copy(value):
    return json.loads(channel._canonical(value))


def _digest(value):
    return hashlib.sha256(channel._canonical(value).encode()).hexdigest()


def _bindings():
    paths=(Path(__file__),*(Path(m.__file__) for m in (field,reference,atomic,dipole,full,channel,modes,integer_time)))
    return {p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}


def _matrix(record):
    return field._matrix(record)


def _norm(matrix,bits):
    centre,error=full._midpoint_matrix(matrix,bits)
    return field._price_upper(full._norm(centre)+full._operator_bound(error),bits)


def _exponential(real,imag,bits):
    quantum=1<<(bits+32)
    r,i=Q(round(real*quantum),quantum),Q(round(imag*quantum),quantum)
    _require(max(real,r)<=Q(1,2),'scalar source growth exceeds its registered bound')
    centre,error=modes.complex_exponential(r,i,bits=bits)
    # |exp(z)-exp(z0)| <= 2|z-z0| along this Re(z)<=1/2 segment.
    price=error+2*(abs(real-r)+abs(imag-i))
    return centre,field._price_upper(price,bits)


def _pairs(matrix,bits):
    centre,error=field._pairs(matrix,bits)
    dyadic=field._quantize(centre,bits)
    return dyadic,field._price_upper(error+field._difference(centre,dyadic),bits)


def _scale(matrix,value):
    return {key:v*value for key,v in matrix.items() if v*value}


def _sum(*matrices):
    result={}
    for matrix in matrices:
        field._add(result,matrix)
    return result


def _precision(bits):
    _require(type(bits) is int and 64<=bits<=512,'registered operator/scalar precision required')


def _scalar(raw,time,bits,carrier=True):
    t=full.exact(time);sigma=Q(raw['sigma_squared_seconds']);centre=Q(raw['centre_seconds'])
    g,ge=_exponential(-(t-centre)**2/(4*sigma),Q(0),bits)
    angle=Q(raw['phase_radians'])-(Q(raw['carrier_angular_frequency_per_second'])*t if carrier else 0)
    phase,pe=_exponential(Q(0),angle,bits) if angle else ((Q(1),Q(0)),Q(0))
    return field._product(g,phase),ge*(abs(phase[0])+abs(phase[1]))+pe*(abs(g[0])+abs(g[1]))+ge*pe


def _parts(raw,bits):
    h=_matrix(raw['complete_static_H_per_second']);loss=_matrix(raw['complete_natural_R_per_second'])
    a=_matrix(raw['source_raising_operator_per_second'])
    phase,pe=_exponential(Q(0),Q(raw['phase_radians']),bits) if Q(raw['phase_radians']) else ((Q(1),Q(0)),Q(0))
    raising=_scale(a,dipole.ComplexRadical(*phase))
    drive=_scale(_sum(raising,dipole.matrix_adjoint(raising)),dipole.ComplexRadical(0,-1))
    p={(i,i):dipole.ComplexRadical(1) for i,s in enumerate(dipole.STATES) if s.family=='D2'}
    quiet=_sum(_scale(h,dipole.ComplexRadical(0,-1)),_scale(loss,Q(-1,2)),
               _scale(p,dipole.ComplexRadical(0,Q(raw['carrier_angular_frequency_per_second']))))
    k,ek=_pairs(quiet,bits);v,ev=_pairs(drive,bits)
    ev+=2*pe*_norm(a,bits)
    return k,ek,v,ev,_norm(_sum(_scale(a,dipole.ComplexRadical(0,-1)),
                              _scale(dipole.matrix_adjoint(a),dipole.ComplexRadical(0,-1))),bits)


def _envelope_polynomial(raw,start,width,order,bits):
    sigma=Q(raw['sigma_squared_seconds']);offset=start-Q(raw['centre_seconds'])
    b=offset*width/(2*sigma);c=width**2/(4*sigma);radius=abs(b)+c
    _require(radius<=Q(1,2),'Gaussian source slice needs refinement before polynomial checking')
    value,error=_exponential(-offset**2/(4*sigma),Q(0),bits)
    coefficients=[Q(0)]*(2*order+1)
    for k in range(order+1):
        for j in range(k+1):
            coefficients[k+j]+=Q(comb(k,j),factorial(k))*(-b)**(k-j)*(-c)**j
    tail=2*radius**(order+1)/factorial(order+1)
    return [value[0]*x for x in coefficients],2*error+tail


def _piece(raw,piece,current,start,mode_bits,bits,envelope_order,parts):
    _require(type(piece) is dict and set(piece)=={'duration_seconds','modes'} and
        type(piece['modes']) is list and piece['modes'],'complete untrusted operator modes required')
    width=full.exact(piece['duration_seconds']);_require(width>0,'positive physical operator slice required')
    k,ek,v,ev,drive_norm=parts
    gaussian,tail=_envelope_polynomial(raw,start,width,envelope_order,bits)
    initial={};end={};residual=Q(0);rounding=Q(0);scalar_error=Q(0);terms=[]
    for mode in piece['modes']:
        _require(type(mode) is dict and set(mode)=={'lambda_per_second','coefficients'} and
            type(mode['lambda_per_second']) is list and len(mode['lambda_per_second'])==2 and
            type(mode['coefficients']) is list and 1<=len(mode['coefficients'])<=65,
            'untrusted full33 exponential-polynomial operator witness required')
        lr,li=map(full.exact,mode['lambda_per_second'])
        _require(lr*width<=Q(1,2),'mode growth exceeds the certified physical slice')
        growth=Q(1) if lr<=0 else Q(2)
        coefficients=[field._read_entries(c,mode_bits) for c in mode['coefficients']]
        field._scaled_add(initial,coefficients[0],1)
        defects=[{} for _ in range(len(coefficients)+len(gaussian)-1)]
        integral=Q(0);polynomial={}
        for n,matrix in enumerate(coefficients):
            field._scaled_add(defects[n],field._left(k,matrix),width)
            field._scaled_add(defects[n],{key:field._product((lr*width,li*width),x) for key,x in matrix.items()},-1)
            if n:
                field._scaled_add(defects[n-1],matrix,-n)
            optical=field._left(v,matrix)
            for j,value in enumerate(gaussian):
                field._scaled_add(defects[n+j],optical,width*value)
            integral+=field._norm(matrix)/Q(n+1)
            field._scaled_add(polynomial,matrix,1)
        paid=growth*sum((field._norm(d)/Q(n+1) for n,d in enumerate(defects)),Q(0))
        coefficient_price=width*growth*integral*(ek+ev*sum(map(abs,gaussian))+drive_norm*tail)
        exponential,e=_exponential(lr*width,li*width,bits)
        field._scaled_add(end,{key:field._product(exponential,x) for key,x in polynomial.items()},1)
        evaluation=e*field._norm(polynomial)
        residual+=paid;rounding+=coefficient_price;scalar_error+=evaluation
        terms.append({'lambda_per_second':[str(lr),str(li)],'polynomial_degree':len(coefficients)-1,
            'true_K_polynomial_residual_price':str(paid),'source_coefficient_and_Gaussian_tail_price':str(coefficient_price),
            'endpoint_mode_evaluation_price':str(evaluation),'curve_norm_time_integral_upper':str(width*growth*integral)})
    join=field._difference(current,initial)
    uniform=join+residual+rounding
    return width,end,uniform+scalar_error,{'physical_slice_seconds':[str(start),str(start+width)],
        'join_operator_error':str(join),'true_K_polynomial_residual_price':str(residual),
        'source_coefficient_and_Gaussian_tail_price':str(rounding),'endpoint_mode_evaluation_price':str(scalar_error),
        'uniform_rotating_curve_error_from_piece_input':str(uniform),'complete_mode_prices':terms,
        'Gaussian_polynomial_degree':2*envelope_order,'Gaussian_uniform_remainder_upper':str(tail),
        'operator_amplitude_Hermitian_projected':False,'exact_eigen_relation_assumed':False}


def _integer_matrix(matrix,bits):
    quantum=1<<bits
    return {key:{1:(int(a*quantum),int(b*quantum))} for key,(a,b) in matrix.items() if a or b}


def _integer_add(target,matrix,real=1,imag=0):
    for key,terms in matrix.items():
        a,b=terms[1];old=target.get(key,{}).get(1,(0,0))
        value=(old[0]+real*a-imag*b,old[1]+imag*a+real*b)
        if value==(0,0):
            target.pop(key,None)
        else:
            target[key]={1:value}


def _integer_norm(matrix,denominator,bits):
    rows,columns={},{}
    for (i,j),terms in matrix.items():
        a,b=terms[1];weight=abs(a)+abs(b)
        rows[i]=rows.get(i,0)+weight;columns[j]=columns.get(j,0)+weight
    if not rows:
        return Q(0)
    _,upper=full._sqrt(max(rows.values())*max(columns.values()),bits)
    return upper/denominator


def _piece_integer(raw,piece,current,start,mode_bits,bits,envelope_order,parts):
    _require(type(piece) is dict and set(piece)=={'duration_seconds','modes'} and
        type(piece['modes']) is list and piece['modes'],'complete untrusted operator modes required')
    width=full.exact(piece['duration_seconds']);_require(width>0,'positive physical operator slice required')
    k,ek,v,ev,drive_norm=parts
    gaussian,tail=_envelope_polynomial(raw,start,width,envelope_order,bits)
    work_bits=bits+32;work_quantum=1<<work_bits;mode_quantum=1<<mode_bits
    operators=[];compiled_error=Q(0)
    for j,g in enumerate(gaussian):
        exact={};field._scaled_add(exact,v,width*g)
        if j==0:
            field._scaled_add(exact,k,width)
        rounded=field._quantize(exact,work_bits)
        compiled_error+=field._difference(exact,rounded)
        operators.append(_integer_matrix(rounded,work_bits))
    generator_error=compiled_error+width*(ek+ev*sum(map(abs,gaussian))+drive_norm*tail)
    initial={};end={};residual=Q(0);rounding=Q(0);scalar_error=Q(0);terms=[]
    for mode in piece['modes']:
        _require(type(mode) is dict and set(mode)=={'lambda_per_second','coefficients'} and
            type(mode['lambda_per_second']) is list and len(mode['lambda_per_second'])==2 and
            type(mode['coefficients']) is list and 1<=len(mode['coefficients'])<=65,
            'untrusted full33 exponential-polynomial operator witness required')
        lr,li=map(full.exact,mode['lambda_per_second']);_require(lr*width<=Q(1,2),'mode growth exceeds the certified physical slice')
        growth=Q(1) if lr<=0 else Q(2)
        matrices=[field._read_entries(c,mode_bits) for c in mode['coefficients']]
        coefficients=[_integer_matrix(m,mode_bits) for m in matrices]
        field._scaled_add(initial,matrices[0],1)
        lam=(round(lr*width*work_quantum),round(li*width*work_quantum))
        lambda_error=abs(lr*width-Q(lam[0],work_quantum))+abs(li*width-Q(lam[1],work_quantum))
        defects=[{} for _ in range(len(coefficients)+len(operators)-1)]
        integral=Q(0);polynomial={}
        for n,coefficient in enumerate(coefficients):
            for j,operator in enumerate(operators):
                if operator and coefficient:
                    _integer_add(defects[n+j],integer_time._integer_product(operator,coefficient))
            _integer_add(defects[n],coefficient,-lam[0],-lam[1])
            if n:
                _integer_add(defects[n-1],coefficient,-n*work_quantum)
            integral+=_integer_norm(coefficient,mode_quantum,bits)/Q(n+1)
            field._scaled_add(polynomial,matrices[n],1)
        paid=growth*sum((_integer_norm(m,mode_quantum*work_quantum,bits)/Q(n+1)
                        for n,m in enumerate(defects)),Q(0))
        coefficient_price=growth*integral*(generator_error+lambda_error)
        exponential,e=_exponential(lr*width,li*width,bits)
        field._scaled_add(end,{key:field._product(exponential,x) for key,x in polynomial.items()},1)
        evaluation=e*field._norm(polynomial)
        residual+=paid;rounding+=coefficient_price;scalar_error+=evaluation
        terms.append({'lambda_per_second':[str(lr),str(li)],'polynomial_degree':len(coefficients)-1,
            'true_K_polynomial_residual_price':str(paid),'source_coefficient_and_Gaussian_tail_price':str(coefficient_price),
            'endpoint_mode_evaluation_price':str(evaluation),'curve_norm_time_integral_upper':str(width*growth*integral)})
    join=field._difference(current,initial);uniform=join+residual+rounding
    return width,end,uniform+scalar_error,{'physical_slice_seconds':[str(start),str(start+width)],
        'join_operator_error':str(join),'true_K_polynomial_residual_price':str(residual),
        'source_coefficient_and_Gaussian_tail_price':str(rounding),'endpoint_mode_evaluation_price':str(scalar_error),
        'uniform_rotating_curve_error_from_piece_input':str(uniform),'complete_mode_prices':terms,
        'Gaussian_polynomial_degree':2*envelope_order,'Gaussian_uniform_remainder_upper':str(tail),
        'common_integer_residual_denominator_bits':work_bits+mode_bits,
        'all_K_polynomial_rounding_paid':True,'operator_amplitude_Hermitian_projected':False,'exact_eigen_relation_assumed':False}


def _source_blocks(raw):
    neighbors={i:{i} for i in range(33)}
    for matrix in (_matrix(raw['complete_static_H_per_second']),_matrix(raw['source_raising_operator_per_second'])):
        for i,j in matrix:
            neighbors[i].add(j);neighbors[j].add(i)
    remaining=set(neighbors);blocks=[]
    while remaining:
        pending=[min(remaining)];block=set()
        while pending:
            i=pending.pop()
            if i not in block:
                block.add(i);pending.extend(neighbors[i]-block)
        remaining-=block;blocks.append(tuple(sorted(block)))
    return blocks


def _restore(raw,matrix,start,stop,bits):
    omega=Q(raw['carrier_angular_frequency_per_second']);phases={};result={};errors={}
    for key,value in matrix.items():
        i,j=key
        angle=omega*((start if dipole.STATES[j].family=='D2' else 0)-
                     (stop if dipole.STATES[i].family=='D2' else 0))
        if angle not in phases:
            phases[angle]=_exponential(Q(0),angle,bits) if angle else ((Q(1),Q(0)),Q(0))
        phase,error=phases[angle];result[key]=dipole.ComplexRadical(*field._product(phase,value))
        errors[key]=error*(abs(value[0])+abs(value[1]))
    return result,full._operator_bound(errors)


class GaussianAtomicPulseSource:
    def __init__(self,parent,side,*,sigma_squared_seconds,centre_seconds,duration_seconds,phase_radians=0):
        _CHECK();field._closed(parent)
        _require(type(parent) is reference.ReferenceLocalPhaseSource and type(side) is int and side in (0,1),
            'closed same reference local parent and original side required; G or prepared rho is not input')
        original=reference.ReferenceLocalPhaseSource.record(parent)
        plan=original['source_generated_local_plans'][side]
        _require(plan[-1]['raw_controls']['kind']=='excitation','the same parent needs its original final excitation controls')
        sigma,centre,duration,phase=map(full.exact,(sigma_squared_seconds,centre_seconds,duration_seconds,phase_radians))
        _require(sigma>0 and duration>0 and 0<=centre<=duration,'positive Gaussian variance and physical certification horizon required')
        owner=atomic.MunichAtomicProgramme.from_record(original['working_atomic_owner'])
        old_phase=atomic._read_phase(plan[-1]['source_phase']);programme=atomic.AtomicPhase.programme(old_phase)
        _require(len(programme.tones)==1 and programme.tones[0].name=='excitation' and programme.tones[0].line=='D2',
            'one source-owned D2 excitation tone required')
        quiet=field._source(owner,side);unit=Q(original['working_atomic_owner']['atomic_base']['seconds_per_unit'])
        raising=_scale(programme._excitation(programme.tones[0]),1/unit)
        self._parent=parent
        self._frame={'schema':SCHEMA,'reference_local_parent':original,'side':side,
            'working_atomic_owner':original['working_atomic_owner'],'working_common_optical_source':original['working_common_optical_source'],
            'working_aperture_source':original['working_aperture_source'],'reference_clock':original['reference_clock'],
            'original_constant_excitation_controls':plan[-1],
            'sigma_squared_seconds':str(sigma),'centre_seconds':str(centre),'duration_seconds':str(duration),'phase_radians':str(phase),
            'carrier_angular_frequency_per_second':str(programme.tones[0].angular_frequency/unit),
            'source_raising_operator_per_second':channel._input_record(raising),
            'complete_static_H_per_second':quiet['full_H_per_second'],'complete_natural_R_per_second':quiet['full_R_per_second'],
            'original_physical_natural_jumps':quiet['original_physical_natural_jumps'],
            'intensity_rule':'I_peak exp[-(t-t_c)^2/(2 sigma_squared)]',
            'field_rule':'raw_peak exp[-(t-t_c)^2/(4 sigma_squared)] exp[-i omega*t+i phase]',
            'duration_is_certification_horizon':True,'Gaussian_zero_at_endpoint_assumed':False,'hard_AOM_mask_installed':False,
            'source_refs':{'G2015':'section2.3.2 p21 and section4.2.2 Eq4.1 p66; declared approximate-Gaussian apparatus family',
                'G2021':'section2.3.1-2 pp13-14; resonance and nominal polarization roles'},
            'source_scope':'declared Gaussian raw field family; its peak, variance, centre and phase are inverse coordinates',
            'raw_peak_is_actual_pi_pulse_certification':False,'public_2015_values_are_2016_run_membership':False,
            'K_identity':'K(t)+K(t)*+R=0 on all33 coordinates',
            'ground_absorption_or_one_photon_per_arm_assumed':False,'physical_target_state_supplied':False,
            'emission_history_not_traced_to_pulse_endpoint':True,'controller_advance':False,'source_bindings':_bindings()}
        self._seal=_digest(self._frame);_ISSUED.add(self._seal)

    def record(self):
        _CHECK();field._closed(self)
        _require(type(self) is GaussianAtomicPulseSource and set(vars(self))=={'_parent','_frame','_seal'} and
            self._seal in _ISSUED and _digest(self._frame)==self._seal and self._frame['source_bindings']==_bindings() and
            reference.ReferenceLocalPhaseSource.record(self._parent)==self._frame['reference_local_parent'],
            'Gaussian raw controls, same reference parent or executed source changed')
        return _copy(self._frame)

    @classmethod
    def from_record(cls,record):
        _require(cls is GaussianAtomicPulseSource and type(record) is dict and record.get('schema')==SCHEMA,'closed Gaussian source record required')
        parent=reference.ReferenceLocalPhaseSource.from_record(record['reference_local_parent'])
        result=cls(parent,record['side'],**{name:record[name] for name in
            ('sigma_squared_seconds','centre_seconds','duration_seconds','phase_radians')})
        _require(result.record()==record,'source-generated H, bath, Gaussian envelope or clock changed')
        return result

    def hamiltonian_jet(self,time,order=0,*,bits=192):
        _precision(bits);_require(type(order) is int and 0<=order<=32,'finite original source derivative order required')
        raw=GaussianAtomicPulseSource.record(self);t=full.exact(time)
        scalar,error=_scalar(raw,t,bits);raising=_matrix(raw['source_raising_operator_per_second'])
        slope=(-(t-Q(raw['centre_seconds']))/(2*Q(raw['sigma_squared_seconds'])),
               -Q(raw['carrier_angular_frequency_per_second']))
        second=-1/(2*Q(raw['sigma_squared_seconds']));p=(Q(1),Q(0));previous=(Q(0),Q(0));jets=[]
        for n in range(order+1):
            value=field._product(p,scalar);a=_scale(raising,dipole.ComplexRadical(*value))
            h=_sum(a,dipole.matrix_adjoint(a),_matrix(raw['complete_static_H_per_second']) if n==0 else {})
            jets.append({'order':n,'complete_H_derivative':channel._input_record(h),
                'scalar_operator_error_upper':str(field._price_upper(2*error*(abs(p[0])+abs(p[1]))*_norm(raising,bits),bits))})
            following=field._product(slope,p)
            following=(following[0]+n*second*previous[0],following[1]+n*second*previous[1])
            previous,p=p,following
        return {'source_record_digest':self._seal,'physical_local_seconds':str(t),'jets':jets,'scalar_bits':bits,
                'full_Z_and_all_allowed_D2_edges_retained':True}

    def generator(self,time,*,bits=192):
        raw=GaussianAtomicPulseSource.record(self)
        jet=GaussianAtomicPulseSource.hamiltonian_jet(self,time,bits=bits)['jets'][0]
        h=_matrix(jet['complete_H_derivative']);loss=_matrix(raw['complete_natural_R_per_second'])
        k=_sum(_scale(h,dipole.ComplexRadical(0,-1)),_scale(loss,Q(-1,2)))
        _require(not _sum(k,dipole.matrix_adjoint(k),loss),'complete physical no-jump loss identity failed')
        return {'source_record_digest':self._seal,'physical_local_seconds':str(time),
            'complete_H':channel._input_record(h),'complete_K':channel._input_record(k),'complete_R':channel._input_record(loss),
            'scalar_operator_error_upper':jet['scalar_operator_error_upper'],'K_plus_Kadj_plus_R_is_zero':True}

    def hamiltonian(self,time,*,bits=192):
        jet=GaussianAtomicPulseSource.hamiltonian_jet(self,time,bits=bits)['jets'][0]
        return _matrix(jet['complete_H_derivative']),Q(jet['scalar_operator_error_upper'])

    def Gamma_math_price(self,start,stop,*,bits=192):
        raw=GaussianAtomicPulseSource.record(self);s,t=map(full.nonnegative,(start,stop));_require(s<=t,'ordered physical source interval required')
        clock=raw['reference_clock'];gamma=Q(clock['Gamma_numerical_centre']);lo,hi=map(Q,clock['angular_Gamma_enclosure_per_second'])
        delta=max(abs(gamma-lo),abs(hi-gamma));upper=max(gamma,hi)
        a=_norm(_matrix(raw['source_raising_operator_per_second']),bits)/gamma
        fixed=(_norm(_matrix(raw['complete_static_H_per_second']),bits)+
               _norm(_matrix(raw['complete_natural_R_per_second']),bits)/2)/gamma+2*a
        omega=abs(Q(raw['carrier_angular_frequency_per_second'])/gamma)
        return field._price_upper(delta*((t-s)*fixed+upper*omega*a*(t*t-s*s)),bits)

    def field_off_tail_price(self,after,*,bits=192):
        raw=GaussianAtomicPulseSource.record(self);sigma=Q(raw['sigma_squared_seconds']);x=full.exact(after)-Q(raw['centre_seconds'])
        if x>0:
            value,error=_exponential(-x*x/(4*sigma),Q(0),bits)
            integral=2*sigma*(abs(value[0])+error)/x
        else:
            _,upper=full._sqrt(sigma.numerator*sigma.denominator,bits)
            integral=6*upper/sigma.denominator
        norm=_norm(_matrix(raw['source_raising_operator_per_second']),bits)
        return {'source_record_digest':self._seal,'after_physical_local_seconds':str(after),
            'field_envelope_tail_integral_seconds_upper':str(integral),
            'no_jump_operator_Duhamel_price_upper':str(2*norm*integral),
            'density_CP_Duhamel_price_per_input_norm_upper':str(4*norm*integral),
            'Gaussian_tail_set_to_zero':False,'actual_field_off_command_identified':False}

    def generate_operator_trials(self,start,stop,*,slices=16,order=0,mode_bits=160,coefficient_bits=192):
        """Small source eigensolves propose witnesses, never their correctness."""
        import numpy as np
        _precision(mode_bits);_precision(coefficient_bits)
        raw=GaussianAtomicPulseSource.record(self);s,t=map(full.nonnegative,(start,stop))
        _require(s<=t<=Q(raw['duration_seconds']) and type(slices) is int and slices>0 and
                 type(order) is int and 0<=order<=64,'ordered source interval and registered slice/polynomial budget required')
        k,ek,v,ev,_=_parts(raw,coefficient_bits);current={(i,i):(Q(1),Q(0)) for i in range(33)}
        pieces=[];blocks=_source_blocks(raw)
        if s<t:
            while any(abs((a-Q(raw['centre_seconds']))*(t-s)/slices/(2*Q(raw['sigma_squared_seconds'])))+
                ((t-s)/slices)**2/(4*Q(raw['sigma_squared_seconds']))>Q(1,2)
                for a in (s,t)):
                slices*=2
            for j in range(slices):
                a=s+(t-s)*j/slices;width=(t-s)/slices;mid=a+width/2
                g,_=_exponential(-(mid-Q(raw['centre_seconds']))**2/(4*Q(raw['sigma_squared_seconds'])),Q(0),coefficient_bits)
                point=dict(k);field._scaled_add(point,v,g[0])
                gaussian,_=_envelope_polynomial(raw,a,width,max(8,(order+1)//2),coefficient_bits)
                proposals=[];endpoint={}
                for block in blocks:
                    def array(matrix):
                        return np.array([[complex(*map(float,matrix.get((i,l),(0,0)))) for l in block] for i in block])
                    operator=array(point);drive=array(v);prior=array(current)
                    beginning=array(k)+float(gaussian[0])*drive
                    values,vectors=np.linalg.eig(operator);inverse=np.linalg.inv(vectors)
                    for n,value in enumerate(values):
                        terms=[np.outer(vectors[:,n],inverse[n,:])@prior];images=[drive@terms[0]]
                        for degree in range(order):
                            following=(beginning-value*np.eye(len(block)))@terms[degree]
                            for jg in range(1,min(degree,len(gaussian)-1)+1):
                                following+=float(gaussian[jg])*images[degree-jg]
                            following*=float(width)/(degree+1)
                            terms.append(following);images.append(drive@following)
                        coefficients=[];polynomial={}
                        for term in terms:
                            coefficient={}
                            for ib,i in enumerate(block):
                                for jb,l in enumerate(block):
                                    z=term[ib,jb]
                                    if z:
                                        coefficient[i,l]=(Q.from_float(float(z.real)),Q.from_float(float(z.imag)))
                            coefficient=field._quantize(coefficient,mode_bits)
                            coefficients.append(field._entries(coefficient,mode_bits));field._scaled_add(polynomial,coefficient,1)
                        exponent=(Q.from_float(float(value.real)),Q.from_float(float(value.imag)))
                        proposals.append({'lambda_per_second':list(map(str,exponent)),'coefficients':coefficients})
                        scalar,_=_exponential(exponent[0]*width,exponent[1]*width,coefficient_bits)
                        field._scaled_add(endpoint,{key:field._product(scalar,z) for key,z in polynomial.items()},1)
                pieces.append({'duration_seconds':str(width),'modes':proposals});current=endpoint
        return {'schema':SCHEMA+'/untrusted-operator-curve','source_record':raw,
            'source_interval_seconds':list(map(str,(s,t))),'mode_bits':mode_bits,'pieces':pieces,
            'initial_operator_is_I_at_interval_start':True,'writer_correctness_assumed':False}

    def certify_operator(self,trial,*,coefficient_bits=192,phase_bits=192,envelope_order=8):
        _precision(coefficient_bits);_precision(phase_bits)
        raw=GaussianAtomicPulseSource.record(self)
        _require(type(trial) is dict and trial.get('schema')==SCHEMA+'/untrusted-operator-curve' and trial.get('source_record')==raw,
            'untrusted modes must belong to the same original Gaussian source')
        _require(type(envelope_order) is int and 0<=envelope_order<=16,'finite source Gaussian polynomial order required')
        s,t=map(full.nonnegative,trial['source_interval_seconds']);_precision(trial['mode_bits'])
        _require(s<=t<=Q(raw['duration_seconds']) and type(trial['pieces']) is list,'ordered full physical two-time source interval required')
        current={(i,i):(Q(1),Q(0)) for i in range(33)};error=Q(0);elapsed=s;prices=[]
        parts=_parts(raw,coefficient_bits)
        for piece in trial['pieces']:
            width,current,local,payment=_piece_integer(raw,piece,current,elapsed,trial['mode_bits'],phase_bits,envelope_order,parts)
            _require(elapsed+width<=t,'operator witness crossed the certified source clock')
            payment['uniform_rotating_operator_error_upper']=str(error+Q(payment['uniform_rotating_curve_error_from_piece_input']))
            payment['previous_rotating_endpoint_error']=str(error)
            error+=local;elapsed+=width;prices.append(payment)
        _require(elapsed==t,'complete two-time operator interval must be covered')
        endpoint,frame_error=_restore(raw,current,s,t,phase_bits) if s<t else (
            {(i,i):dipole.ComplexRadical(1) for i in range(33)},Q(0))
        gamma=GaussianAtomicPulseSource.Gamma_math_price(self,s,t,bits=coefficient_bits)
        result={'schema':SCHEMA+'/two-time-operator-certificate','source_record':raw,'untrusted_trial':_copy(trial),
            'source_interval_seconds':list(map(str,(s,t))),'full33_operator':channel._input_record(endpoint),
            'rotating_operator_error':str(error),'frame_endpoint_scalar_price':str(frame_error),'Gamma_math_operator_price':str(gamma),
            'operator_norm_error_upper':str(error+frame_error+gamma),'complete_piece_prices':prices,
            'coefficient_bits':coefficient_bits,'phase_bits':phase_bits,'envelope_order':envelope_order,
            'outward_price_rounding':{'rule':'ceil nonnegative prices on the registered dyadic grid',
                'scalar_argument_guard_bits':32,'scalar_argument_change_price':'2*(abs(delta_real)+abs(delta_imag)); Re<=1/2',
                'increment_upper_per_scalar_ceil':str(Q(1,1<<phase_bits)),
                'increment_upper_per_coefficient_or_Gamma_ceil':str(Q(1,1<<coefficient_bits)),
                'compiled_K_coefficient_change_paid_by_operator_norm':True,'integer_output_limit_disabled':False},
            'frame_rule':'U(t,s)=D(t) V(t,s) D(s)*; D(t)=exp[-i omega*t P_D2]',
            'initial_operator':'I at s','operator_amplitude_Hermitian_projected':False,'inverse_U_t0_used':False,
            'uniform_curve_prices_exclude_individual_numeric_frame_evaluations':True,
            'source_emission_history_or_future_Gaussian_tail_traced':False,'source_bindings':_bindings()}
        _REPORTS.add(_digest(result));return _copy(result)

    def verify_operator(self,report):
        raw=GaussianAtomicPulseSource.record(self)
        _require(type(report) is dict and report.get('schema')==SCHEMA+'/two-time-operator-certificate' and
            report.get('source_record')==raw and report.get('source_bindings')==_bindings(),'same closed Gaussian operator report required')
        if _digest(report) not in _REPORTS:
            expected=GaussianAtomicPulseSource.certify_operator(self,report['untrusted_trial'],**{name:report[name] for name in
                ('coefficient_bits','phase_bits','envelope_order')})
            _require(expected==report,'two-time input, complete K residual, field phase or price changed')
        return True


def _function(value):
    value=getattr(value,'__func__',value)
    return id(value),id(getattr(value,'__code__',None)),repr(getattr(value,'__defaults__',None)),repr(getattr(value,'__kwdefaults__',None))


def _signature():
    helpers=(_require,_copy,_digest,_bindings,_matrix,_norm,_exponential,_pairs,_scale,_sum,_precision,_scalar,_parts,
        _envelope_polynomial,_piece,_integer_matrix,_integer_add,_integer_norm,_piece_integer,_source_blocks,
        _restore,_function,_signature,_check,reference.ReferenceLocalPhaseSource.record,
        reference.ReferenceLocalPhaseSource.from_record,atomic.MunichAtomicProgramme.from_record,
        atomic._read_phase,atomic.AtomicPhase.programme,field._source,field._closed,field._matrix,field._pairs,
        field._left,field._product,field._scaled_add,field._read_entries,field._entries,field._quantize,
        field._difference,field._norm,field._add,field._price_upper,full._midpoint_matrix,full._norm,full._operator_bound,
        full._sqrt,modes.complex_exponential,dipole.matrix_adjoint,channel._input_record,
        integer_time._integer_product,integer_time.gcd)
    methods=tuple(_function(v) for v in vars(GaussianAtomicPulseSource).values() if callable(v) or isinstance(v,classmethod))
    return tuple(map(_function,helpers)),methods,tuple(dipole.STATES),SCHEMA


def _check():
    if _check is not _CHECK or _check.__code__ is not _CHECK_CODE or _signature is not _SIGNATURE or _signature()!=_EXPECTED:
        raise ValueError('Gaussian executed source closure changed')
    field._CHECK()


_SIGNATURE=_signature
_CHECK,_CHECK_CODE=_check,_check.__code__
_EXPECTED=_signature()
