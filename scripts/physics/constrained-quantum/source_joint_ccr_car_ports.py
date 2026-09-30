#!/usr/bin/env python3
"""Actual Gauss100 four-energy Weyl Hamiltonian and its CCR/CAR ports.

This consumes the complete existing Weyl leaf at the original fixed time.  It
normal-orders its actual current squares to expose the cubic fermion feedback.
The variables here are local configuration coordinates, not physical momenta k.
"""
from __future__ import annotations

from collections import defaultdict
from dataclasses import dataclass
from functools import lru_cache
import hashlib
import json
import time
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID
from source_clock_symbol_recursion import SourceWeylLeafFactory
from source_coframe_live_ordering import full
from source_coframe_legendre import rational
from source_gauss_quantum_current import (
    apply_superposition, normal_pair, weighted_sum, encode_state,
)
from scalar_dyson_peierls import annihilate_basis, create_basis
from source_joint_form_hamiltonian import read_bound
from source_quantum_temporal_symbol import N
from source_lorentz_contact import encode
from source_scalar_weyl_symbol import quadratic_weyl_action
from source_common_weyl_symbol import coframe_action


def simplified(state):
    return {w: v for w, c in state.items() if (v := s.factor(c)) != 0}


def same(left, right):
    assert simplified(weighted_sum(((1, left), (-1, right)))) == {}


def car(mode, state, creation=False):
    basis = create_basis if creation else annihilate_basis
    out = defaultdict(lambda: s.S.Zero)
    for word, coefficient in state.items():
        changed, sign = basis(mode, word)
        if sign:
            out[changed] += sign*coefficient
    return simplified(out)


def linear_car(row, state, creation=False):
    return simplified(weighted_sum((c, car(int(j), state, creation))
        for j, c in enumerate(row) if c))


@dataclass
class NormalSymbol:
    scalar: s.Expr
    one_body: s.MatrixBase
    pairs: tuple  # (coefficient, A, B): normalProduct(A,B), with full504 matrices

    def apply(self, state):
        terms = [(self.scalar, state), (1, apply_superposition(self.one_body, state))]
        for coefficient, A, B in self.pairs:
            for word, value in state.items():
                terms.append((coefficient*value, normal_pair(A, B, word)))
        return simplified(weighted_sum(terms))

    def fermion_port(self, mode, state, creation=False):
        """Full i[H,a] or i[H,a†], including every original cubic term."""
        assert 0 <= mode < 504
        if creation:
            terms = [(s.I, linear_car(self.one_body[:, mode], state, True))]
            for coefficient, A, B in self.pairs:
                terms.extend(((s.I*coefficient,
                    linear_car(A[:, mode], apply_superposition(B, state), True)),
                    (s.I*coefficient,
                    linear_car(B[:, mode], apply_superposition(A, state), True))))
        else:
            terms = [(-s.I, linear_car(self.one_body[mode, :], state))]
            for coefficient, A, B in self.pairs:
                terms.extend(((-s.I*coefficient,
                    apply_superposition(B, linear_car(A[mode, :], state))),
                    (-s.I*coefficient,
                    apply_superposition(A, linear_car(B[mode, :], state)))))
        return simplified(weighted_sum(terms))

    def adjoint(self):
        return NormalSymbol(s.conjugate(self.scalar), self.one_body.H,
            tuple((s.conjugate(c), B.H, A.H) for c,A,B in self.pairs))

    def derivative(self, variable, point=None, negative=False):
        """Leibniz differentiates both live CAR matrices, not just weights."""
        def d(value):
            ans = value.diff(variable)
            return ans.subs(point) if point else ans
        def at(value):
            return value.subs(point) if point else value
        pairs = []
        for c, A, B in self.pairs:
            dc, dA, dB = d(c), d(A), d(B)
            if dc: pairs.append((dc, at(A), at(B)))
            if dA.todok(): pairs.append((at(c), dA, at(B)))
            if dB.todok(): pairs.append((at(c), at(A), dB))
        sign = -1 if negative else 1
        return NormalSymbol(sign*d(self.scalar), s.SparseMatrix(sign*d(self.one_body)),
            tuple((sign*c, s.SparseMatrix(A), s.SparseMatrix(B)) for c,A,B in pairs))


class SourceJointCCRCarPorts:
    """No Hamiltonian, pole, current, residue or quantum state is caller-supplied."""
    def __init__(self):
        self.leaf = SourceWeylLeafFactory()
        self.time_point = (N, s.S.Zero, s.S.Zero, s.S.Zero)
        self.time_sub = dict(zip(self.leaf.y, self.time_point))
        self.identity = s.SparseMatrix(s.eye(504))

    def at_time(self, value):
        if isinstance(value, s.MatrixBase):
            return s.SparseMatrix(value).applyfunc(lambda c: s.factor(c.subs(self.time_sub)))
        return s.factor(s.sympify(value).subs(self.time_sub))

    @lru_cache(None)
    def coefficients(self, configuration):
        assert len(configuration) == 100
        q, x, A, scalar, gauge, cf, original = self.leaf.background(configuration)
        v = s.prod(q[j] for j in (0, 2, 5))
        principal = s.SparseMatrix(100, 100, {})
        principal[:6, :6] = cf['K']
        principal[6:, 6:] = self.at_time(scalar['principal']+gauge['principal'])
        linear_identity = s.zeros(100, 1)
        linear_identity[6:, :] = self.at_time(scalar['momentum_identity']+gauge['momentum_identity'])
        qsub = dict(zip(self.leaf.weyl.native.joint.coframe.q, q))
        linear_current = [self.at_time(full(M.subs(qsub))) for M in self.leaf.pairing['Mh']]
        weights = self.at_time(scalar['momentum_current']+gauge['momentum_current'])
        for j in range(94):
            linear_current.append(s.SparseMatrix(sum(
                (c*self.leaf.charges[a] for a,c in enumerate(weights[j,:]) if c),
                s.SparseMatrix(504, 504, {}))))
        constant = self.at_time(sum(d[k] for d in (scalar,gauge) for k in
            ('classical_zero','half_density_potential','weyl_correction')))+N*(s.Rational(5,4)/v+3*v)
        matrix = self.at_time(original['matter_CAR']+full(cf['one_body']+cf['correction']))
        matrix += N*s.Rational(21,16)/v*self.identity
        pairs = [(N*s.Rational(3,16)/v, self.identity, self.identity)]
        charges = self.leaf.charges
        for d in (scalar,gauge):
            for a,c in enumerate(self.at_time(d['linear_current'])):
                if c: matrix += c*charges[a]
            for (a,b),c in self.at_time(d['square_current']).todok().items():
                matrix += c*(charges[a]*charges[b])
                pairs.append((c,charges[a],charges[b]))
        currents = [s.SparseMatrix(full(J)) for J in cf['J']]
        pairs.extend((c,currents[a],currents[b]) for (a,b),c in cf['W'].todok().items())
        assert principal == principal.T
        return {'principal':principal,'linear_identity':linear_identity,
            'linear_current':tuple(linear_current),'zero':NormalSymbol(s.factor(constant),
                s.SparseMatrix(matrix).applyfunc(s.factor),tuple(pairs)),
            'coordinates':tuple(configuration),'coframe':cf,'scalar':scalar,'gauge':gauge,
            'matter':original,'volume':v}

    def symbol(self, phase200):
        assert len(phase200)==200
        d=self.coefficients(tuple(phase200[:100]));p=s.Matrix(phase200[100:]);zero=d['zero']
        scalar=zero.scalar+(p.T*d['principal']*p)[0]+(p.T*d['linear_identity'])[0]
        matrix=zero.one_body+sum((p[j]*M for j,M in enumerate(d['linear_current']) if p[j]),
            s.SparseMatrix(504,504,{}))
        return NormalSymbol(s.factor(scalar),s.SparseMatrix(matrix).applyfunc(s.factor),zero.pairs)

    def velocity(self, coordinate, phase200):
        assert 0<=coordinate<100
        d=self.coefficients(tuple(phase200[:100]));p=s.Matrix(phase200[100:])
        return NormalSymbol(s.factor(2*(d['principal'][coordinate,:]*p)[0]+d['linear_identity'][coordinate]),
            d['linear_current'][coordinate],())

    def force(self, coordinate, phase200):
        """Actual -∂z_j sigma_H. Every requested original coordinate is evaluable."""
        assert 0<=coordinate<100
        variable=s.Dummy('source_configuration_'+str(coordinate),positive=True) if coordinate in (0,2,5) else s.Dummy('source_configuration_'+str(coordinate),real=True)
        argument=list(phase200);argument[coordinate]=variable
        return self.symbol(argument).derivative(variable,{variable:phase200[coordinate]},negative=True)

    def force_and_velocity_gradient(self, coordinate, phase200):
        """One common source differentiation generates force and all100 mixed ports."""
        variable=s.Dummy('source_configuration_'+str(coordinate),positive=True) if coordinate in (0,2,5) else s.Dummy('source_configuration_'+str(coordinate),real=True)
        argument=list(phase200);argument[coordinate]=variable
        point={variable:phase200[coordinate]}
        force=self.symbol(argument).derivative(variable,point,negative=True)
        gradients=tuple(self.velocity(j,argument).derivative(variable,point) for j in range(100))
        return force,gradients


def word_normal(word):
    """Finite exact CAR reduction; labels are actual modes, no matrix truncation."""
    if not word: return {():1}
    for k in range(len(word)-1):
        left,right=word[k:k+2]
        if left[0]==right[0] and left[1]==right[1]: return {}
        if (left[0]<right[0]) or (left[0]==right[0] and left[1]>right[1]):
            swapped=word[:k]+(right,left)+word[k+2:]
            out={w:-c for w,c in word_normal(swapped).items()}
            if left[0]==0 and right[0]==1 and left[1]==right[1]:
                for w,c in word_normal(word[:k]+word[k+2:]).items():out[w]=out.get(w,0)+c
            return {w:c for w,c in out.items() if c}
    return {word:1}


def ordered_partitions(length):
    if length==0:yield ();return
    for row in ordered_partitions(length-1):
        for j in range(max(row,default=-1)+2):yield row+(j,)


def verify_universal_car_ports():
    """Each equality pattern of five indices; no finite-carrier premise."""
    checked=0
    for i,j,k,ell,m in ordered_partitions(5):
        q=((1,i),(0,j));r=((1,k),(0,ell));quartic=((1,i),(1,k),(0,ell),(0,j))
        for creation in (False,True):
            generator=((int(creation),m),)
            lhs=defaultdict(int)
            for c,w in ((1,quartic+generator),(-1,generator+quartic)):
                for key,value in word_normal(w).items():lhs[key]+=c*value
            terms=[]
            if creation:
                if j==m:terms.append((1,((1,i),)+r))
                if ell==m:terms.append((1,((1,k),)+q))
            else:
                if i==m:terms.append((-1,r+((0,j),)))
                if k==m:terms.append((-1,q+((0,ell),)))
            rhs=defaultdict(int)
            for c,w in terms:
                for key,value in word_normal(w).items():rhs[key]+=c*value
            assert {w:c for w,c in lhs.items() if c}=={w:c for w,c in rhs.items() if c},(i,j,k,ell,m,creation)
            checked+=1
    return checked


def main():
    began=time.monotonic()
    deps=('source_common_weyl_symbol','source_joint_form_hamiltonian','source_full_quantum_adjoint')
    for name in deps:read_bound(name)
    universal=verify_universal_car_ports()
    print('PASS complete CAR equality patterns:',universal,flush=True)
    model=SourceJointCCRCarPorts();m=model.leaf.weyl
    q=(s.Rational(7,6),s.Rational(1,11),s.Rational(9,8),-s.Rational(1,13),s.Rational(1,17),s.Rational(11,10))
    x=s.zeros(61,1);x[19]=s.Rational(1,100)
    A=m.section.A0.copy();A[0,2]+=s.Rational(1,31);A[1,7]+=s.Rational(1,19)
    point=s.Matrix(q).col_join(x).col_join(A.reshape(36,1))
    configuration=tuple(point[i] for i in model.leaf.free)
    momenta=tuple(s.Rational(j%7-3,53) for j in range(100))
    phase=configuration+momenta
    d=model.coefficients(configuration);symbol=model.symbol(phase)
    print('PASS actual Gauss100 full504 normal coefficients:',len(symbol.pairs),'quartic factors',flush=True)
    words=((),(144,),(144,396),(5,144,396))
    images=[];m=model.leaf.weyl;p=s.Matrix(momenta)
    qsub=dict(zip(m.native.joint.coframe.q,q))
    divergence=s.zeros(100,1)
    divergence[:6,:]=model.at_time(model.leaf.pairing['divergence'].subs(qsub))
    divergence[6:,:]=model.at_time(d['scalar']['div_principal']+d['gauge']['div_principal'])
    divdiv=model.at_time(sum(s.diff(model.leaf.pairing['K'][i,j],m.native.joint.coframe.q[i],
        m.native.joint.coframe.q[j]) for i in range(6) for j in range(6)).subs(qsub))
    divdiv+=model.at_time(d['scalar']['divdiv_principal']+d['gauge']['divdiv_principal'])
    divlinear=model.at_time(d['scalar']['div_momentum_identity']+d['gauge']['div_momentum_identity'])
    divweights=model.at_time(d['scalar']['div_momentum_current']+d['gauge']['div_momentum_current'])
    divmatrix=sum((c*Q for c,Q in zip(divweights,model.leaf.charges)),s.SparseMatrix(504,504,{}))
    ordering=s.factor(-s.I*(divergence.T*p)[0]-divdiv/4-s.I*divlinear/2)
    def native_action(values,gs,hs):
        terms=[]
        has_value=any(values.values())
        # Every original component is linear in the finite input jet; avoid
        # rebuilding an entire coframe square for its exactly zero q-jet.
        if has_value or any(g[6:,:].todok() for g in gs.values()) or any(h[6:,6:].todok() for h in hs.values()):
            for component in ('scalar','gauge'):
                terms.append((1,quadratic_weyl_action(d[component],values,gs,hs,m.current_word,m.current)))
        if has_value or any(g[:6,:].todok() for g in gs.values()) or any(h[:6,:6].todok() for h in hs.values()):
            terms.append((1,coframe_action(m,{'coframe':d['coframe'],'e':d['matter']['e']},
                model.leaf.pairing,values,gs,hs)))
        if has_value:
            terms.append((1,apply_superposition(d['matter']['matter_CAR'],values)))
        return simplified({w:model.at_time(c) for w,c in weighted_sum(terms).items()})
    def native_plane_action(state):
        return native_action(state,{w:c*s.I*p for w,c in state.items()},
            {w:-c*p*p.T for w,c in state.items()})
    for word in words:
        state={word:s.S.One}
        expected=native_action(state,{word:s.I*p},{word:-p*p.T})
        image=symbol.apply(state)
        quantized=simplified(weighted_sum(((1,image),(ordering,state),
            (-s.I/2,apply_superposition(divmatrix,state)))))
        same(quantized,expected);assert expected
        images.append({'input':list(word),'symbol_image':encode_state(image),
            'unchanged_differential_H':encode_state(expected)})
    print('PASS full four-energy Weyl quantization against original joint differential H in four CAR sectors',flush=True)
    state={(144,396):s.S.One};velocity_nonzero=[]
    for j in range(100):
        velocity=model.velocity(j,phase)
        g=s.eye(100)[:,j];h=s.I*(g*p.T+p*g.T)
        values={(144,396):s.S.Zero};gs={(144,396):g};hs={(144,396):h}
        commutator=simplified({w:s.I*c for w,c in native_action(values,gs,hs).items()})
        expected=simplified(weighted_sum(((1,velocity.apply(state)),(-s.I*divergence[j],state))))
        same(commutator,expected);velocity_nonzero.append(bool(expected))
        if j in (5,30,60,99):print('PASS original differential CCR port',j+1,'/100',flush=True)
    print('PASS all100 source CCR commutators against unchanged joint differential H',flush=True)
    car_checks=[];cubic_nonzero=0
    for word in ((144,396),(5,144,396)):
        value={word:s.S.One};Hvalue=symbol.apply(value);native_Hvalue=native_plane_action(value)
        for mode in (5,144,145,258,396,397):
            for creation in (False,True):
                actual=symbol.fermion_port(mode,value,creation)
                direct=simplified(weighted_sum(((s.I,symbol.apply(car(mode,value,creation))),
                    (-s.I,car(mode,Hvalue,creation)))))
                same(actual,direct)
                native_port=simplified(weighted_sum(((s.I,native_plane_action(car(mode,value,creation))),
                    (-s.I,car(mode,native_Hvalue,creation)))))
                quantum_order=NormalSymbol(s.S.Zero,-s.I*divmatrix/2,()).fermion_port(mode,value,creation)
                same(native_port,weighted_sum(((1,actual),(1,quantum_order))))
                linear=NormalSymbol(s.S.Zero,symbol.one_body,()).fermion_port(mode,value,creation)
                defect=simplified(weighted_sum(((1,actual),(-1,linear))))
                cubic_nonzero+=bool(defect)
                car_checks.append({'word':list(word),'mode':mode,'creation':creation,
                    'symbol_image':encode_state(actual),'original_differential_port':encode_state(native_port),
                    'cubic':encode_state(defect)})
    assert cubic_nonzero
    print('PASS actual CAR Heisenberg direct composition:',len(car_checks),'ports; nonzero cubic:',cubic_nonzero,flush=True)
    force,mixed=model.force_and_velocity_gradient(0,phase)
    force_image=force.apply(state);assert force_image
    mixed_images=[port.apply(state) for port in mixed]
    assert any(mixed_images)
    derivative_variable=s.Dummy('joint_CAR_current_parameter',real=True)
    argument=list(phase);argument[0]=derivative_variable
    live=model.symbol(argument);at={derivative_variable:phase[0]}
    # Independently differentiate the actual i[H,a] action, retaining dA,dB.
    force_car=[]
    for creation in (False,True):
        image=live.fermion_port(144,state,creation)
        derivative=simplified({w:s.diff(c,derivative_variable).subs(at) for w,c in image.items()})
        predicted=force.fermion_port(144,state,creation)
        same(derivative,{w:-c for w,c in predicted.items()})
        force_car.append(encode_state(predicted))
    print('PASS live source coframe force, all100 mixed velocities, and CAR/CCR mixed Jacobi',flush=True)
    sharp=symbol.adjoint()
    sharp_image=sharp.apply(state)
    Yraw=d['matter']['matter']['Y'];E_inverse=d['matter']['matter']['inverse_E']
    Yprimal=model.at_time(-s.I*d['matter']['e'].det()*E_inverse*Yraw)
    Y=s.SparseMatrix(s.diag(Yprimal,-Yprimal.conjugate()))
    same(sharp_image,weighted_sum(((1,symbol.apply(state)),(1,apply_superposition(Y.H-Y,state)))))
    print('PASS independent original Hsharp=H0+Ydagger; H0+Y unchanged',flush=True)
    files=[HERE/(name+'.json') for name in deps]+[HERE/(name+'.py') for name in (
        'source_joint_ccr_car_ports','source_clock_symbol_recursion','source_scalar_weyl_symbol',
        'source_common_weyl_symbol','source_gauss_quantum_current','source_coframe_live_ordering')]+[HERE/'JointCCRCarPorts.lean']
    result={'root':ROOT_ID,'scope':'ACTUAL_LOCAL_GAUSS100_FULL504_CCR_CAR_HEISENBERG_PORTS',
        'source_sha256':model.leaf.weyl.graph.common.source_hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'same_H':'The unchanged complete source Weyl leaf is normal-ordered using QQ=Q(AB)+normalProduct(A,B). All order-zero density/Weyl terms, original Y, current contractions and quartic contact remain.',
        'time':list(map(str,model.time_point)),'configuration100':list(map(str,configuration)),
        'configuration_momenta100':list(map(str,momenta)),
        'CCR':{'position_count':100,'momentum_count':100,'position':'OpW(partial_p sigma_H)',
            'momentum':'-OpW(partial_z sigma_H); actual finite source derivative API force(j,phase)',
            'actual_position_nonzero':sum(velocity_nonzero),'canonical_momenta_are_not_external_k':True},
        'CAR':{'modes':504,'annihilator_ports':504,'creator_ports':504,'primal_branch':252,'independent_real_branch':252,
            'annihilation':'-i sum_j M_mj a_j -i sum_ab c_ab [sum_j A_mj Q(B)a_j + sum_j B_mj Q(A)a_j]',
            'creation':'i sum_j M_jm a†_j +i sum_ab c_ab [sum_j A_jm a†_jQ(B)+sum_j B_jm a†_jQ(A)]',
            'five_index_equality_cases':universal,
            'Lean_ports':['SourceJointCCRCarPorts.normalProduct_primal_port',
                'SourceJointCCRCarPorts.normalProduct_independent_momentum_port'],'quartic_factors':len(symbol.pairs),
            'nonzero_actual_cubic_checks':cubic_nonzero},
        'actual_full_H_images':images,'actual_CAR_ports':car_checks,
        'actual_force':{'coordinate':0,'image':encode_state(force_image),
            'mixed_velocity_nonzero':sum(bool(row) for row in mixed_images),
            'CAR_mixed_Jacobi':force_car,'original_Hsharp_image':encode_state(sharp_image)},
        'common_operator_core':'C_c_infinity of the original regular Gauss100 chart tensor the full exterior CAR504 algebra. All source coefficients are smooth on this chart and each differential operator has finite order; no global extension or unitary evolution is selected here.',
        'scope_of_next_consumer':'The local homogeneous Gauss100 source has exact Heisenberg ports. Spatial field development/physical k and the full four-block retarded response still require their original source splice; no auxiliary F(C)=0 is assumed.',
        'proton_lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'seconds':round(time.monotonic()-began,3)}
    (HERE/'source_joint_ccr_car_ports.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS source joint CCR/CAR ports',result['seconds'],'seconds',flush=True)


if __name__=='__main__':main()
