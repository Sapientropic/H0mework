#!/usr/bin/env python3
"""Original full-CAR clock through the first nonzero canonical Moyal order.

The source phase two-jet supplies every scalar Moyal contraction. All native
Weyl zero-order terms, ordinary Jordan subprincipal terms, and original Y are
retained. These are generated symbols on the source cone, not a summed clock
operator or a spectral measure.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import json
import time
import sympy as s

from source_clock_subprincipal import (
    SourceClockSubprincipal, operator_pair, apply_pair, combination, zero,
    HERE, ROOT, ROOT_ID, bound, decode, encode, rational, equal, full,
    apply_superposition, weighted_sum, encode_state, matrix_grade, state_grade, N)
from source_gauss_quantum_current import normal_pair
from source_full_quantum_adjoint import split_matter
from source_clock_principal_jets import Jet, moyal2


def source_matrix_grade(A,weight):
    for (i,j),value in A.todok().items():
        zero((int(int(i)%63<7)-int(int(j)%63<7)-weight)*value)


def reduced(state): return {w:s.factor(v) for w,v in state.items() if s.factor(v)!=0}


def add(*states):return reduced(weighted_sum((1,state) for state in states))


def scale(c,state):return reduced(weighted_sum([(c,state)]))


def state_equal(a,b):assert not add(a,scale(-1,b))


def source_jet(record):
    return Jet(s.sympify(record['value']),decode(record['gradient200']),decode(record['Hessian200']))


class SourceClockSecondOrder:
    def __init__(self):
        self.sub=SourceClockSubprincipal();m=self.sub; self.y=m.y;f=m.factors
        self.at=m.source_clock;self.Jinv=rational(m.J.inv())
        self.charges=[s.SparseMatrix(Q) for Q in m.weyl.charges]
        self.cf=f['data']['coframe'];self.Jcf=[s.SparseMatrix(full(J)) for J in self.cf['J']]
        self.cf_one=s.SparseMatrix(full(self.cf['one_body']+self.cf['correction']))
        equal(self.cf_one.H,self.cf_one);source_matrix_grade(self.cf_one,0)
        pair=s.MutableSparseMatrix.zeros(64,64)
        for (a,b),v in self.cf['W'].todok().items():
            for (i,j),l in self.cf['J'][a].todok().items():
                for (k,h),r in self.cf['J'][b].todok().items():pair[8*i+k,8*j+h]+=v*l*r
        equal(rational(pair.H-pair),s.zeros(64))
        for Q in self.charges:equal(Q.H,Q);source_matrix_grade(Q,0)
        for d in (m.scalar,m.gauge):
            equal(d['square_current'].T,d['square_current'])
            equal(d['square_current'].conjugate(),d['square_current'])
            equal(d['linear_current'].conjugate(),d['linear_current'])
            zero(s.im(d['classical_zero']+d['half_density_potential']+d['weyl_correction']))
        data=m.cone.original.coefficients(self.y,f['q'],f['x'],f['A'])
        self.M0,self.Y=split_matter(data);equal(self.M0.H,self.M0)
        source_matrix_grade(self.M0,0);source_matrix_grade(self.Y,1)
        self.force1_derivatives=[]
        for a in range(4):
            self.force1_derivatives.append([operator_pair(
                -s.diff(m.H1['identity'],self.y[a],self.y[b]).subs(self.at),
                -m.H1['current'].diff(self.y[a],self.y[b]).subs(self.at)) for b in range(4)])
        self.force2_Hessian=[s.Matrix(4,4,lambda b,c:s.factor(-s.diff(m.H2,self.y[a],self.y[b],self.y[c]).subs(self.at))) for a in range(4)]
        for row in self.force1_derivatives:
            for op in row:zero(s.im(op['identity']));equal(op['current'].H,op['current']);source_matrix_grade(op['current'],0)
        for H in self.force2_Hessian:equal(H.T,H);equal(H.conjugate(),H)

    def quadratic_zero(self,data,state):
        scalar=data['classical_zero']+data['half_density_potential']+data['weyl_correction']
        result=[(scalar,state)]
        currents=[apply_superposition(Q,state) for Q in self.charges]
        result.extend((c,currents[a]) for a,c in enumerate(data['linear_current']) if c)
        result.extend((c,apply_superposition(self.charges[a],currents[b])) for (a,b),c in data['square_current'].todok().items())
        return reduced(weighted_sum(result))

    def coframe_zero(self,state):
        m=self.sub;v=m.factors['volume'];pieces=[]
        for word,value in state.items():
            number=len(word)
            pieces.extend((value*weight/N,normal_pair(self.Jcf[a],self.Jcf[b],word)) for (a,b),weight in self.cf['W'].todok().items())
            pieces.append((value*((3*number**2+18*number+20)/(16*v)+3*v),{word:1}))
        pieces.append((1/N,apply_superposition(self.cf_one,state)))
        return scale(self.y[0],reduced(weighted_sum(pieces)))

    def zero_components(self,state):
        return {'coframe':self.coframe_zero(state),'scalar_form':self.quadratic_zero(self.sub.scalar,state),
            'gauge':self.quadratic_zero(self.sub.gauge,state),'matter_noY':reduced(apply_superposition(self.M0,state)),
            'original_Y':reduced(apply_superposition(self.Y,state))}

    def actual_consumer(self,principal):
        m=self.sub;word=(144,396);state={word:s.S.One}
        point=principal['source_covector'];equal(m.p,decode(point['canonical_p100']))
        A=source_jet(principal['a0_2']);T=source_jet(principal['traceS2']);C=source_jet(principal['principal_clock'])
        zero(C.value-N)
        force_geometry=s.factor((moyal2(C,T*C.power(-2))/C.value+moyal2(C,T*C.power(-1))/C.value**2)/16)
        zero(force_geometry-s.sympify(principal['original_lapse_force_second_Moyal']))
        assert force_geometry!=0
        energy_geometry=s.factor(-moyal2(C,A)/8+moyal2(C,T*C.power(-1))/(16*C.value))
        components=self.zero_components(state)
        Hzero=add(*components.values());H0zero=add(*(v for key,v in components.items() if key!='original_Y'))
        force0=[reduced({w:-s.diff(v,y).subs(self.at) for w,v in Hzero.items()}) for y in self.y]
        force0_grade0=[reduced({w:-s.diff(v,y).subs(self.at) for w,v in H0zero.items()}) for y in self.y]
        Yvalue=reduced({w:v.subs(self.at) for w,v in components['original_Y'].items()})
        state_equal(add(force0[0],scale(-1,force0_grade0[0])),scale(-1/N,Yvalue))
        for a in range(1,4):state_equal(force0[a],force0_grade0[a])
        C1=[apply_pair(c,state) for c in m.clock]
        @lru_cache(None)
        def clock_product(b,c):
            return scale(s.Rational(1,2),add(apply_pair(m.clock[b],C1[c]),apply_pair(m.clock[c],C1[b])))
        crossed=[];quadratic=[];residual=[];residual_grade0=[]
        for a in range(4):
            linear=[]
            for b in range(4):
                derivative=self.force1_derivatives[a][b]
                linear.append(scale(s.Rational(1,2),add(apply_pair(m.clock[b],apply_pair(derivative,state)),apply_pair(derivative,C1[b]))))
            crossed.append(add(*linear))
            quadratic.append(add(*(scale(self.force2_Hessian[a][b,c]/2,clock_product(b,c)) for b in range(4) for c in range(4))))
            geo=scale(force_geometry,state) if a==0 else {}
            residual.append(add(force0[a],crossed[a],quadratic[a],geo))
            residual_grade0.append(add(force0_grade0[a],crossed[a],quadratic[a],geo))
        clock2=[add(*(scale(-self.Jinv[a,b],residual[b]) for b in range(4))) for a in range(4)]
        clock2_grade0=[add(*(scale(-self.Jinv[a,b],residual_grade0[b]) for b in range(4))) for a in range(4)]
        for a in range(4):
            assert not add(residual[a],*(scale(m.J[a,b],clock2[b]) for b in range(4)))
            state_grade(clock2_grade0[a],2,0)
            raising=add(clock2[a],scale(-1,clock2_grade0[a]));state_grade(raising,2,1)
            expected=scale(-s.Rational(324,625),Yvalue) if a==0 else {}
            state_equal(raising,expected)
        assert any(clock2)
        missing_geometry=[add(clock2[a],scale(self.Jinv[a,0]*force_geometry,state)) for a in range(4)]
        assert add(clock2[0],scale(-1,missing_geometry[0]))
        # The original energy is retracted by the same graph, not evaluated by
        # ordinary commuting substitution. Its pure Moyal term differs from F0.
        H0point=reduced({w:v.subs(self.at) for w,v in Hzero.items()})
        energy_cross=add(*(scale(-s.Rational(1,2),add(apply_pair(m.clock[a],apply_pair(m.force[a],state)),apply_pair(m.force[a],C1[a]))) for a in range(4)))
        energy_quadratic=add(*(scale(-m.J[a,b]/2,clock_product(a,b)) for a in range(4) for b in range(4)))
        energy0=add(H0point,energy_cross,energy_quadratic,scale(energy_geometry,state))
        # Actual source four-force stationarity annihilates every C_-2 term in
        # the energy at this order; this is generated by the same principal H.
        for a in range(4):zero(s.diff(m.H2,self.y[a]).subs(self.at))
        return {'input_CAR':list(word),'original_zero_order_Weyl_components':{k:encode_state(reduced({w:v.subs(self.at) for w,v in image.items()})) for k,image in components.items()},
            'four_original_force_order0':[encode_state(v) for v in force0],
            'four_subprincipal_Jordan_terms':[encode_state(v) for v in crossed],
            'four_principal_quadratic_clock_terms':[encode_state(v) for v in quadratic],
            'actual_scalar_Moyal_force':str(force_geometry),'actual_scalar_Moyal_energy':str(energy_geometry),
            'four_clock_order_minus2':[encode_state(v) for v in clock2],
            'four_grade0_clock_order_minus2':[encode_state(v) for v in clock2_grade0],
            'full_Y_clock_order_minus2':encode_state(scale(-s.Rational(324,625),Yvalue)),
            'full_Y_clock_coefficient':'-324/625','all4_corrected_force_order0_residuals_zero':True,
            'omitting_Moyal_clock_defect':encode_state(add(clock2[0],scale(-1,missing_geometry[0]))),
            'first_reduced_energy_order0':encode_state(energy0),
            'first_reduced_energy_components':{'original_Weyl_H0_plus_Y':encode_state(H0point),'Jordan_clock_H1':encode_state(energy_cross),
                'principal_clock_quadratic':encode_state(energy_quadratic),'canonical_Moyal':encode_state(scale(energy_geometry,state))},
            'particle_scope':'Actual state (144,396) in the original full504 two-particle CAR fiber at the source canonical100 phase point; original Gauss-section coefficient derivatives are retained in the complete Weyl symbol.'}


def main():
    start=time.monotonic();model=SourceClockSecondOrder()
    names=('source_clock_subprincipal','independent_source_clock_subprincipal','source_clock_principal_jets','independent_source_clock_principal_jets',
        'source_principal_clock_cone','independent_source_principal_clock_cone','source_common_weyl_symbol',
        'independent_source_common_weyl_symbol','source_coframe_weyl_symbol','independent_source_coframe_weyl_symbol')
    paid={name:bound(name) for name in names}
    actual=model.actual_consumer(paid['source_clock_principal_jets']['actual_consumer'])
    print('PASS original full-CAR force degree0, both Jordan clock terms and actual200phase Moyal correction',flush=True)
    print('PASS source N2 complete clock order-minus2 and reduced energy order0; original raising Y coefficient -324/625',flush=True)
    files=[HERE/(name+'.json') for name in names]+[HERE/name for name in ('source_clock_second_order.py','source_clock_subprincipal.py',
        'source_clock_principal_jets.py','source_common_weyl_symbol.py','source_scalar_weyl_symbol.py','source_coframe_weyl_symbol.py',
        'source_gauss_quantum_current.py')]
    out={'root':ROOT_ID,'scope':'SOURCE_FULL_N2_FIRST_NONZERO_CANONICAL_MOYAL_CLOCK_AND_REDUCED_ENERGY_COEFFICIENT',
        'source_sha256':model.sub.cone.native.graph.common.source_hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'generation':'C_-2=-J2^-1*(F0+sum_b Jordan(C_-1,b,partial_yb F1)+sum_bc partial_yb_yc F2 Jordan(C_-1,b,C_-1,c)/2+Moyal2(F2,C0))',
        'canonical_order':'The first Jordan Poisson terms cancel against scalar leading clock/principal atoms. Matrix C_-1 with matrix degree1 atoms first contributes a phase derivative one order below this coefficient; no C_-1 phase derivative is discarded here.',
        'all_original_zero_order_terms':'Coframe ordered normal pair, live onebody and number half-density/Weyl scalar; scalar/gauge complete94-variable graph inverses and rho corrections; full matter H0 and original Y.',
        'grade0_Hermitian_mechanism':'Original coframe pair tensor and onebody are Hermitian; scalar/gauge quadratic current weights are real symmetric; matter H0 is Hermitian. Every new cross term is an ordinary Jordan product of generated Hermitian grade0 factors with real force tensors.',
        'actual_consumer':actual,'complete_quantum_clock_operator_or_spectral_measure_generated':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-start,3)}
    (HERE/'source_clock_second_order.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('PASS source clock second canonical order',out['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
