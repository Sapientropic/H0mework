#!/usr/bin/env python3
"""Independent original-coefficient audit of the coframe volume/shape form.

The candidate is never imported. The BF primary graph is rebuilt by the raw
reader; exterior-slot CAR and literal polynomial differentiation test the
complete covariant square, including its scalar divergence correction.
"""
from __future__ import annotations

from collections import defaultdict
from itertools import combinations
import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_coframe_live_ordering import (
    RawLiveCoefficients, HERE, ROOT, ROOT_ID, rational, full, terms, current,
    polynomial_action, state_encode)
from independent_source_gauge_legendre import bindings, decode, encode
from independent_source_gauss_quantum_current import columns, decoded_state


def simp(x):
    return x.applyfunc(s.simplify) if isinstance(x, s.MatrixBase) else s.simplify(x)


def eq(a, b):
    difference = simp(a-b)
    assert not difference.todok() if isinstance(difference, s.MatrixBase) else difference == 0, difference


def state_eq(a, b):
    for word in a.keys() | b.keys():
        eq(s.expand((s.sympify(a.get(word, 0))-s.sympify(b.get(word, 0))).rewrite(s.exp)), 0)


def exterior_minors(U, word):
    support = sorted({row for (row, col), value in U.todok().items() if col in word and value != 0})
    result = {}
    for output in combinations(support, len(word)):
        value = simp(U.extract(output, word).det())
        if value != 0: result[output] = value
    return result


class RawVolumeShape:
    def __init__(self):
        self.raw = RawLiveCoefficients(); c = self.raw
        self.q = s.Matrix(c.q); q = self.q
        self.v = q[0]*q[2]*q[5]
        self.r = s.Symbol('volume_radius', positive=True)
        self.theta = s.Matrix(s.symbols('shape_u shape_w shape_a shape_b shape_c', real=True))
        self.m = s.Symbol('particle_number', integer=True, nonnegative=True)
        self.x = s.Matrix([self.r, *self.theta])
        u, w, a, b, z = self.theta
        self.forward = self.r**s.Rational(2, 3)*s.Matrix([s.exp(u), a, s.exp(w), b, z, s.exp(-u-w)])
        self.backward = s.Matrix([s.sqrt(self.v), s.log(q[0]/self.v**s.Rational(1, 3)),
            s.log(q[2]/self.v**s.Rational(1, 3)), q[1]/self.v**s.Rational(1, 3),
            q[3]/self.v**s.Rational(1, 3), q[4]/self.v**s.Rational(1, 3)])
        self.sub = dict(zip(q, self.forward)); self.J = self.backward.jacobian(q)
        forward_J = self.forward.jacobian(self.x)
        eq(forward_J.det(), 2*self.r**3)
        eq(self.at_shape(self.J)*forward_J, s.eye(6))
        eq(forward_J*self.at_shape(self.J), s.eye(6))
        eq(self.at_shape(self.backward), self.x)
        eq(self.forward.subs(dict(zip(self.x, self.backward)), simultaneous=True), q)
        eq(self.at_shape(self.v), self.r**2)
        # The source pairing is fixed, so this density is its coordinate pullback.
        eq(self.at_shape(self.v**(self.m+2))*forward_J.det(), 2*self.r**(2*self.m+7))
        transformed = self.at_shape(self.J*c.K*self.J.T)/c.N
        eq(transformed[0, 0], s.Rational(3, 16))
        eq(transformed[0, 1:], s.zeros(1, 5))
        self.A = simp(self.r**2*transformed[1:, 1:])
        assert self.r not in self.A.free_symbols
        self.divA = s.Matrix([sum(s.diff(self.A[i, j], self.theta[i]) for i in range(5)) for j in range(5)])
        loggrad = s.Matrix([s.diff(self.v, qj)/self.v for qj in q])
        self.t = rational(c.K*loggrad)
        raw_drift = rational(s.I*c.drift.T+self.m*self.t)
        inverse_H = [s.hessian(y, q) for y in self.backward]
        transformed_drift = self.at_shape(s.Matrix([
            -sum(c.K[i, j]*H[i, j] for i in range(6) for j in range(6))-(self.J[k, :]*raw_drift)[0]
            for k, H in enumerate(inverse_H)]))/c.N
        eq(transformed_drift[0], -3*(2*self.m+7)/(16*self.r))
        eq(transformed_drift[1:, :]*self.r**2, -self.divA)
        hermitian_M = [rational(c.M[j]+s.I*self.t[j]*s.eye(8)) for j in range(6)]
        all_mixed = [self.at_shape(sum((self.J[i, j]*hermitian_M[j] for j in range(6)), s.zeros(8)))/c.N for i in range(6)]
        eq(all_mixed[0], s.zeros(8))
        self.mixed = [simp(M*self.r**2) for M in all_mixed[1:]]
        eq(sum((M.diff(self.theta[i]) for i, M in enumerate(self.mixed)), s.zeros(8)), s.zeros(8))
        self.V = s.Matrix([[1,0,0,0,0],[0,1,0,0,0],[0,a,s.exp(u),0,0],
            [-b,-b,0,s.exp(u),a],[-z,-z,0,0,s.exp(w)]])
        self.G = s.diag(s.Matrix([[s.Rational(1,3),-s.Rational(1,6)],[-s.Rational(1,6),s.Rational(1,3)]]),s.eye(3))
        eq(-self.V*self.G*self.V.T, self.A)
        assert self.G.eigenvals() == {s.Rational(1,6):1,s.Rational(1,2):1,s.S.One:3}
        self.divV = s.Matrix([sum(s.diff(self.V[i,j],self.theta[i]) for i in range(5)) for j in range(5)])
        eq(self.divV,s.Matrix([-2,-1,0,0,0]))
        # Solve the original first-order coefficients for the spin connection.
        inverse = self.G.inv()*self.V.inv()
        self.B = [simp(-sum((inverse[j,i]*self.mixed[i]/2 for i in range(5)),s.zeros(8))) for j in range(5)]
        assert all(not B.free_symbols for B in self.B)
        for j,B in enumerate(self.B):
            eq(B.H,B); eq(B*B,s.zeros(8) if j<2 else s.eye(8)/16)
        eq(self.B[0],s.zeros(8)); eq(self.B[1],s.zeros(8))
        eq(sum((self.divV[i]*self.G[i,j]*self.B[j] for i in range(5) for j in range(5)),s.zeros(8)),s.zeros(8))
        self.quarter = (self.divV.T*self.G*self.divV)[0]/4
        eq(self.quarter,s.Rational(1,4))
        # Construct the actual two-spin operator directly from ordered slots.
        pair = s.MutableSparseMatrix.zeros(64,64)
        for (a0,b0),weight in c.W.todok().items():
            for (i,j),left in c.J[a0].todok().items():
                for (k,l),right in c.J[b0].todok().items():
                    pair[8*i+k,8*j+l] += self.v*weight*left*right/c.N
        self.pair = rational(pair)
        assert not self.pair.free_symbols
        eq(self.pair.H,self.pair)
        self.pair_bound = max(sum(abs(self.pair[i,j]) for j in range(64)) for i in range(64))
        self.onebody = rational(self.v*(c.one_body+c.correction)/c.N)
        eq(self.onebody,-9*s.eye(8)/4)
        self.radial_potential=3*(2*self.m+7)*(2*self.m+5)/64
        # Scalar expansion of the complete covariant square is generic in theta.
        driftQ=s.Matrix([sum(self.G[i,j]*(sum(self.V[k,i]*s.diff(self.V[a,j],self.theta[k]) for k in range(5))+
            (self.divV[j]*self.V[a,i]+self.divV[i]*self.V[a,j])/2) for i in range(5) for j in range(5)) for a in range(5)])
        eq(driftQ,-self.divA)
        for a in range(5):
            eq(2*sum((self.V[a,i]*self.G[i,j]*self.B[j] for i in range(5) for j in range(5)),s.zeros(8)),-self.mixed[a])

    def at_shape(self, expression):
        return simp(expression.subs(self.sub, simultaneous=True))

    def compare(self, candidate):
        symbols={str(z):z for z in [*self.q,*self.x,self.m]}
        for name,value in [('shape_principal',self.A),('source_vector_fields',self.V),('constant_positive_Gram',self.G),('original_onebody',self.onebody)]:
            eq(decode(candidate[name],symbols),value)
        for actual,expected in zip(candidate['constant_spin8_connection'],self.B): eq(decode(actual),expected)
        normal=decode(candidate['original_normal_current_tensor'])
        # Different index order: row/out=(i,k), column/in=(j,l).
        for i in range(8):
            for j in range(8):
                for k in range(8):
                    for l in range(8): eq(normal[8*i+j,8*k+l],self.pair[8*i+k,8*j+l])
        eq(s.sympify(candidate['generated_bounds']['original_two_spin_operator_row_bound']),self.pair_bound)
        expected=s.expand(self.pair_bound*self.m*(self.m-1)+9*self.m/4+3*self.m**2/16+self.radial_potential-self.quarter)
        eq(s.sympify(candidate['generated_bounds']['constant_Cm_norm_bound'],locals=symbols),expected)
        coordinate=candidate['configuration_coordinate_map']
        eq(decode(coordinate['forward'],symbols),self.forward)
        eq(decode(coordinate['inverse'],symbols),self.backward)
        eq(s.sympify(coordinate['positive_Jacobian'],locals=symbols),2*self.r**3)

    def flow_audit(self,candidate):
        t,h=s.symbols('flow_time flow_time_second',real=True)
        symbols={str(z):z for z in [*self.theta,t]}
        rows=[]
        for record in candidate['nonformal_covariant_momentum_flows']['five_global_flows']:
            j=record['index']; flow=decode(record['global_flow'],symbols)
            eq(flow.diff(t),self.V[:,j].subs(dict(zip(self.theta,flow)),simultaneous=True))
            eq(flow.subs(t,0),self.theta)
            eq(flow.subs(t,h).subs(dict(zip(self.theta,flow)),simultaneous=True),flow.subs(t,t+h))
            det=simp(flow.jacobian(self.theta).det())
            eq(det,s.exp(self.divV[j]*t))
            scalar=s.exp(self.divV[j]*t/2)
            eq(scalar**2/det,1)
            U=decode(record['spin_unitary'],symbols)
            eq(U.subs(t,0),s.eye(8)); eq(U.diff(t),s.I*self.B[j]*U)
            eq(U.H*U,s.eye(8)); eq(U.subs(t,t+h),U*U.subs(t,h))
            image=exterior_minors(s.SparseMatrix(full(U)),(144,396))
            state_eq(image,{tuple(w):s.sympify(value,locals=symbols) for w,value in record['actual_N2_image']})
            eq(s.expand(sum(s.conjugate(v)*v for v in image.values()).rewrite(s.exp)),1)
            rows.append({'index':j,'actual_N2_exterior_minors':state_encode(image),'flow_Jacobian':str(det),
                'global_group_law':True,'generator_sign':'d/dt U(t)|0 = i(P_j+dGamma(B_j))'})
        assert len(rows)==5
        # Verify every bracket, including omitted zero brackets.
        saved={(x['left'],x['right']):decode(x['coefficients']) for x in candidate['nonformal_covariant_momentum_flows']['brackets']}
        for i in range(5):
            for j in range(i+1,5):
                bracket=self.V[:,j].jacobian(self.theta)*self.V[:,i]-self.V[:,i].jacobian(self.theta)*self.V[:,j]
                coeff=simp(self.V.inv()*bracket)
                assert not coeff.free_symbols
                eq(coeff,saved.get((i,j),s.zeros(5,1)))
        return rows

    def literal_covariant_square(self,record):
        c=self.raw; word=tuple(record['input_CAR']); m=len(word); unit={word:s.S.One}
        q=tuple(map(s.sympify,record['q'])); qpoint=dict(zip(self.q,q))
        y=simp(self.backward.subs(qpoint)); theta_point=dict(zip(self.theta,y[1:,0])); r=y[0]
        f1=decode(record['configuration_gradient6']); f2=decode(record['configuration_Hessian6'])
        # Differentiate the actual inverse half-density in q, independently of
        # the candidate's transformed radial log-Hessian chain.
        alpha=s.Rational(2*m+7,4)
        logh=alpha*s.log(self.v)
        ell=s.Matrix([s.diff(logh,x) for x in self.q]).subs(qpoint)
        logH=s.hessian(logh,self.q).subs(qpoint)
        J=simp(self.J.subs(qpoint))
        qgradient=simp(J.T*f1-ell)
        qH=simp(J.T*f2*J+sum((f1[a]*s.hessian(self.backward[a],self.q).subs(qpoint) for a in range(6)),s.zeros(6))-
            ell*(J.T*f1).T-(J.T*f1)*ell.T+ell*ell.T-logH)
        eq(qgradient,decode(record['original_q_gradient6'])); eq(qH,decode(record['original_q_Hessian6']))
        data=c.coefficients(q)
        actual,pieces=polynomial_action(data,word,1,qgradient,qH)
        state_eq(actual,decoded_state(record['original_nested_square_image']))
        state_eq(actual,decoded_state(record['volume_shape_image']))
        V=simp(self.V.subs(theta_point)); derivative=[simp(self.V.diff(x).subs(theta_point)) for x in self.theta]
        B=[s.SparseMatrix(full(b)) for b in self.B]
        # Compute each ordered D_i D_j on the full CAR word directly.
        shape_gradient=f1[1:,0]; shape_H=f2[1:,1:]
        square_terms=[]
        for j in range(5):
            inner=terms([(1,current(B[j],unit)),(-s.I*((V[:,j].T*shape_gradient)[0]+self.divV[j]/2),unit)])
            inner_derivatives=[]
            for a in range(5):
                differentiated=(derivative[a][:,j].T*shape_gradient)[0]+(V[:,j].T*shape_H[a,:].T)[0]+self.divV[j]*shape_gradient[a]/2
                inner_derivatives.append(terms([(shape_gradient[a],current(B[j],unit)),(-s.I*differentiated,unit)]))
            for i in range(5):
                if self.G[i,j]==0: continue
                image=terms([(1,current(B[i],inner)),(-s.I*self.divV[i]/2,inner)]+
                    [(-s.I*V[a,i],inner_derivatives[a]) for a in range(5)])
                square_terms.append((self.G[i,j],image))
        Q=terms(square_terms)
        # Rebuild C from the original normal product and one-body pieces.
        _,zero_pieces=polynomial_action(data,word,1,s.zeros(6,1),s.zeros(6))
        native_C=terms([(r**2/c.N,zero_pieces[key]) for key in ('normal_quartic','one_body','coefficient_current')])
        Bsquare=terms((1,current(Bj,current(Bj,unit))) for Bj in B)
        C=terms([(1,native_C),(1,Bsquare),(self.radial_potential.subs(self.m,m)-self.quarter,unit)])
        reconstructed=terms([(-c.N/r**2,Q),(c.N/r**2,C),(-3*c.N*f2[0,0]/16+3*c.N*r**2,unit)])
        state_eq(actual,reconstructed)
        quarter_defect=terms([(c.N/(4*r**2),unit)])
        assert quarter_defect
        assert terms([(1,actual),(-1,reconstructed),(-1,quarter_defect)])
        radial_defect=c.N/r**2*self.radial_potential.subs(self.m,m)
        eq(radial_defect,s.sympify(record['nonzero_omitted_radial_half_density_term']))
        # The direct two-spin reshuffling also reproduces the full distinct-slot
        # normal product on this actual two-particle consumer.
        if m==2:
            from independent_source_gauss_quantum_current import wedge_sort
            pair_image=defaultdict(lambda:s.S.Zero)
            for first,second in ((0,1),(1,0)):
                spin0,fiber0=divmod(word[first],63); spin1,fiber1=divmod(word[second],63)
                col=8*spin0+spin1
                for row in range(64):
                    coefficient=self.pair[row,col]
                    if coefficient==0: continue
                    values=list(word); values[first]=63*(row//8)+fiber0; values[second]=63*(row%8)+fiber1
                    target,sign=wedge_sort(values)
                    if sign: pair_image[target]+=sign*coefficient
            state_eq(terms([(1,pair_image)]),terms([(r**2/c.N,zero_pieces['normal_quartic'])]))
        return {'input_CAR':list(word),'q':list(map(str,q)),'volume_radius':str(r),
            'original_nested_image':state_encode(actual),'literal_minus_Q_plus_C_image':state_encode(reconstructed),
            'omitted_negative_quarter_defect':state_encode(quarter_defect),'omitted_radial_half_density_defect':str(radial_defect),
            'native_normal_product_pair_reshuffle':m==2}


def main():
    began=time.monotonic(); path=HERE/'source_coframe_volume_shape.json'
    candidate=json.loads(path.read_text()); count=bindings(candidate)
    assert candidate['root']==ROOT_ID
    raw=RawVolumeShape(); raw.compare(candidate)
    print('PASS independent BF/primary coefficients, exact volume density, all shape/drift/current coefficients and ordered pair reshuffling',flush=True)
    flows=raw.flow_audit(candidate)
    print('PASS all five global flow group laws, source Jacobians, generator signs and actual CAR exterior minors',flush=True)
    consumers=[raw.literal_covariant_square(row) for row in candidate['actual_fullCAR_consumers']]
    assert [row['input_CAR'] for row in consumers]==[[144],[144,396]]
    print('PASS literal full-CAR -Q+C against original nested action on N1/N2 jets; negative quarter and radial terms retained',flush=True)
    paths=[Path(__file__),path,HERE/'source_coframe_volume_shape.py']+[HERE/name for name in (
        'independent_source_coframe_live_ordering.py','independent_source_coframe_legendre.py',
        'independent_source_lorentz_contact.py','independent_source_gauge_legendre.py','independent_source_gauss_quantum_current.py')]
    result={'verdict':'CERTIFIED_SOURCE_COFRAME_VOLUME_SHAPE_FORM_AND_FIVE_GLOBAL_UNITARY_MOMENTUM_GROUPS',
        'root':ROOT_ID,'candidate_constructor_imported':False,'source_sha256':candidate['source_sha256'],
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        'source_binding_checks':count,'independent_method':'raw original BF epsilon Hessian and primary graph; full coordinate and density derivatives; ordered two-spin tensor; exterior determinants; literal covariant-square and original polynomial nested action',
        'configuration_radius':'sqrt(det spatial coframe), a configuration coordinate, not spatial distance or hadron separation',
        'source_measure':'dq6*v^(m+2)=2*r^(2m+7) dr dtheta5',
        'exact_radial_principal':'3*n/16','radial_shape_mixed':0,
        'generic_shape_differential_coefficients_match':True,'generic_spin8_connection_constant':True,
        'positive_Gram_eigenvalues':['1/6','1/2','1','1','1'],
        'actual_ordered_two_spin_tensor':encode(raw.pair),'ordered_pair_row_norm_bound':str(raw.pair_bound),
        'negative_divergence_scalar_in_C':'-1/4','global_unitary_groups':flows,
        'actual_original_full_CAR_consumers':consumers,
        'whole_occupation_scope':'All finite sectors use the exterior functor of the original 504-mode unitary; the pair term has norm at most row_bound*m*(m-1).',
        'operator_domain_scope':'Explicit complete flows preserve Cc-infinity(shape) tensor finite CAR and yield five strongly continuous unitary groups. No self-adjoint extension of the complete Hamiltonian or spectral/lifetime conclusion is claimed.',
        'full_Hamiltonian_extension_time_root_spectrum_or_lifetime_generated':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-began,3)}
    (HERE/'independent_source_coframe_volume_shape.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS independent source coframe volume/shape',result['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__': main()
