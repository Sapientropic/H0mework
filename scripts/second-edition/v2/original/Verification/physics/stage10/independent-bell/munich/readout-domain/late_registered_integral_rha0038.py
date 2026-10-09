"""Exact finite quadrature of the source's complete late registered effect."""
from dataclasses import dataclass
from fractions import Fraction as Q
from math import factorial
import numpy as np

import late_registered_source_rha0038 as source
import dyadic_matrix_rha0038 as integer

B=integer.BITS
QUANTUM=1 << B


@dataclass
class PricedMatrix:
    centre: dict
    error: Q = Q(0)

    def __post_init__(self):
        source.require(Q(self.error)>=0,'nonnegative arithmetic price required')
        self.error=source.quadrature.upper(self.error,192)

    def norm(self):return integer.norm(self.centre)

    def adjoint(self):return PricedMatrix(integer.adjoint(self.centre),self.error)

    def multiply(self,other):
        centre,rounding=integer.multiply(self.centre,other.centre)
        price=rounding+self.error*other.norm()+other.error*self.norm()+self.error*other.error
        return PricedMatrix(centre,price)

    def scale(self,value,scalar_error=Q(0)):
        centre,rounding=integer.scale(self.centre,value)
        price=rounding+(abs(Q(value[0]))+abs(Q(value[1])))*self.error+scalar_error*(self.norm()+self.error)
        return PricedMatrix(centre,price)


def exact_operator(encoded):
    pairs,error=source.gaussian._pairs(source.gaussian._matrix(encoded),192)
    values={k:(int(a*(1 << 192)),int(b*(1 << 192))) for k,(a,b) in pairs.items()}
    centre,rounding=integer.round_matrix(values,192,B)
    return PricedMatrix(centre,error+rounding)


def polynomial(value):
    source.require(type(value) is dict and set(value)=={'duration_seconds','chebyshev_coefficients'} and
        Q(value['duration_seconds'])==source.PIECE_SECONDS and len(value['chebyshev_coefficients'])==65,
        'the complete checked degree64 one-nanosecond operator piece is required')
    coefficients=[];dropped=Q(0)
    for row in value['chebyshev_coefficients']:
        centre={};seen=set()
        for entry in row:
            source.require(type(entry) is list and len(entry)==4 and all(type(x) is int for x in entry),
                           'canonical full complex dyadic coefficients required')
            i,j,a,b=entry
            source.require(0<=i<33 and 0<=j<33 and (i,j) not in seen and (a or b), 'unique full33 coefficient required')
            seen.add((i,j))
            if source.dipole.STATES[i].family==source.dipole.STATES[j].family:centre[i,j]=a,b
            else:dropped+=Q(abs(a)+abs(b),QUANTUM)
        coefficients.append(centre)
    return coefficients,dropped,sum((integer.norm(c) for c in coefficients),Q(0))


def chebyshev_values(numerator,bits,degree=64):
    quantum=1 << bits;previous=1;current=numerator;scale=1;result=[]
    for n in range(degree+1):
        if n==0:value=previous
        elif n==1:value=current
        else:previous,current=current,2*numerator*current-quantum*quantum*previous;value=current
        if n:scale*=quantum
        exact=Q(value,scale);chosen=round(exact*quantum)
        result.append((chosen,abs(exact-Q(chosen,quantum))))
    return result


def evaluate(coefficients,values,bits):
    centre={};price=Q(0);scale=1 << bits
    for coefficient,(scalar,error) in zip(coefficients,values):
        integer.add(centre,{k:(a*scalar,b*scalar) for k,(a,b) in coefficient.items()})
        price+=error*integer.norm(coefficient)
    rounded,rounding=integer.round_matrix(centre,B+bits,B)
    return PricedMatrix(rounded,price+rounding)


def _array_columns(values,basis):
    real=np.zeros((len(basis),len(values)),dtype=object);imag=real.copy()
    positions={tuple(k):i for i,k in enumerate(basis)}
    for col,value in enumerate(values):
        source.require(set(value.centre)<=set(positions),'line-charge coefficient left the complete source basis')
        for key,(a,b) in value.centre.items():real[positions[key],col]=a;imag[positions[key],col]=b
    return real,imag


def _cross_integral(first,second,basis):
    left=_array_columns(first,basis);right0=_array_columns(second,[[j,i] for i,j in basis])
    right=(right0[0].T,right0[1].T);real,imag=integer.complex_product(left,right)
    independent_real=left[0]@right[0]-left[1]@right[1]
    independent_imag=left[0]@right[1]+left[1]@right[0]
    source.require(np.array_equal(real,independent_real) and np.array_equal(imag,independent_imag),
                   'independent arbitrary-precision integer contraction disagrees')
    centre,rounding=integer.round_matrix({(i,j):(int(real[i,j]),int(imag[i,j]))
        for i in range(len(basis)) for j in range(len(basis)) if real[i,j] or imag[i,j]},2*B,B)
    error=rounding+sum((a.error*b.norm()+b.error*a.norm()+a.error*b.error for a,b in zip(first,second)),Q(0))
    return centre,error,len(basis)**2


def _rows(matrix):return [[i,j,a,b] for (i,j),(a,b) in sorted(matrix.items()) if a or b]


def integrate_piece(program,first,second,index):
    source.require(program['schema']==source.SCHEMA and type(index) is int and 0<=index<60 and
        program['all_physical_natural_baths_retained'] is True and program['same_arm_spectator_no_jump_survival_inserted'] is False,
        'the closed original late source and complete source piece required')
    grid=program['quadrature']['grid'];checked=source.quadrature.check(grid)
    source.require(checked==program['quadrature']['checked'] and checked['registered_accuracy_passed'] is True,
                   'complete positive quadrature certificate changed')
    polynomials=[polynomial(v) for v in (first,second)]
    drop=[p[1] for p in polynomials];norms=[p[2] for p in polynomials]
    eps=[Q(e)+d for e,d in zip(program['late_source_operator_errors'],drop)]
    delta=[4*Q(d)+2*e+e*e for d,e in zip(program['late_source_no_jump_tail_prices_with_Gamma_upper'],eps)]
    joint_delta=delta[0]+delta[1]+delta[0]*delta[1]
    rate_upper=Q(program['Gamma_rate_scale_interval'][1]);rate_delta=Q(program['Gamma_relative_error_upper'])
    dt=source.PIECE_SECONDS;origin=index*dt;bits=grid['bits'];quantum=1 << bits
    moment_error=Q(checked['maximum_moment_defect_upper']);weight_mass=Q(checked['absolute_weight_mass'])
    jumps=[(row,[exact_operator(v) for v in row['local_operators']]) for row in program['complete_detected_jump_rows']]
    same=[[exact_operator(v) for v in side] for side in program['same_arm_effects_scaled_by_piece_seconds']]
    outputs=[[{} for _ in range(4)] for _ in range(2)];numeric=[Q(0)]*4
    cross={(p,line):([],[]) for p in range(4) for line in ('D1','D2')}
    for x,weight in grid['nodes_and_weights']:
        values=chebyshev_values(x,bits);operators=[evaluate(p[0],values,bits) for p in polynomials]
        w=Q(weight,quantum);elapsed=origin+dt*Q(x+quantum,2*quantum)
        phases={line:source.gaussian._exponential(0,Q(f)*elapsed,192) for line,f in program['relative_line_frequencies_per_second'].items()}
        for side,g in enumerate(operators):
            for port,r in enumerate(same[side]):
                image=g.adjoint().multiply(r).multiply(g).scale((w,0))
                integer.add(outputs[side][port],image.centre);numeric[port]+=image.error
        for row,js in jumps:
            port,line=row['port'],row['group'][0];phase,phase_error=phases[line]
            a=operators[0].adjoint().multiply(js[0].adjoint()).multiply(operators[0])
            b=operators[1].adjoint().multiply(js[1]).multiply(operators[1])
            scale=Q(row['physical_rate_per_second'])*dt*w
            a=a.scale((scale*phase[0],scale*phase[1]),scale*phase_error)
            cross[port,line][0].append(a);cross[port,line][1].append(b)
    ports=[]
    for port in range(4):
        coefficient=Q(0);bridge=Q(0);phase_price=Q(0);rate_norm=Q(0);kernels=[]
        for side in (0,1):
            exact_norm=same[side][port].norm()+same[side][port].error
            coefficient+=exact_norm*norms[side]**2
            bridge+=rate_upper*exact_norm*delta[side]
            rate_norm+=exact_norm*(1+eps[side])**2
            source.require(outputs[side][port]==integer.adjoint(outputs[side][port]),'same-arm integral must remain Hermitian')
        for line in ('D1','D2'):
            first_nodes,second_nodes=cross[port,line]
            kernel,price,columns=_cross_integral(first_nodes,second_nodes,program['raised_operator_bases'][line])
            numeric[port]+=2*price
            kernels.append({'line':line,'raised_A_lowered_B_coefficients':_rows(kernel),
                            'conjugate_reverse_term_retained':True,'independent_all_complex_integer_entries':columns})
            frequency=abs(Q(program['relative_line_frequencies_per_second'][line]));radius=frequency*dt
            tail=3*radius**41/factorial(41)
            for row,_ in jumps:
                if row['port']!=port or row['group'][0]!=line:continue
                a,b=map(Q,row['local_operator_norm_bounds']);scaled=Q(row['physical_rate_per_second'])*dt*a*b
                base=2*scaled*norms[0]**2*norms[1]**2
                coefficient+=3*base
                phase_price+=(1+weight_mass)*tail*base
                bridge+=2*rate_upper*scaled*joint_delta
                rate_norm+=2*scaled*(1+eps[0])**2*(1+eps[1])**2
        background=Q(program['original_background_rates_per_second'][port])*dt
        rate_price=rate_delta*(rate_norm+background)
        quad_price=moment_error*coefficient+phase_price
        prices=[source.quadrature.upper(p,192) for p in (numeric[port],quad_price,bridge,rate_price)]
        total=sum(prices,Q(0))
        ports.append({'port':port,'same_arm_A':_rows(outputs[0][port]),'same_arm_B':_rows(outputs[1][port]),
            'source_background_identity_coefficient':str(background),'coherent_cross_kernels':kernels,
            'numeric_exact_arithmetic_and_source_rounding_price':str(prices[0]),
            'complete_polynomial_quadrature_and_phase_price':str(prices[1]),
            'source_full_TP_vs_no_jump_and_curve_price':str(prices[2]),
            'source_Gamma_rate_price':str(prices[3]),'whole_operator_error_upper':str(total)})
    return {'schema':source.SCHEMA+'/checked-piece','source_program_sha256':source.digest(program),'piece_index':index,
        'source_late_relative_interval_seconds':list(map(str,(origin,origin+dt))),'mode_bits':B,'ports':ports,
        'positive_quadrature_points':grid['points'],'complete_polynomial_basis_columns':checked['complete_basis_columns'],
        'source_spectator_reader':'full TP identity','full_natural_recycling_retained':True,
        'source_Gaussian_field_truncated':False,'old_inlet_error_applied_to_effect':False,
        'actual_hardware_uniquely_identified':False,'controller_advance':False}
