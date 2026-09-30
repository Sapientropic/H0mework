#!/usr/bin/env python3
"""Independent implicit native12 slice and broken9 phase-measure audit.

The inverse jet is regenerated from C exp(-alpha.L)b=C b_source,
not from the producer's inverse-forward-Hessian rule. Original native
representations and exterior-slot CAR supply the fields and charged jets.
The full12 configuration Jacobian is kept distinct from Dirac phase measure.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from independent_source_quantum_gauss_section import (
    RawGaussSection, compound, finite_wedge, HERE, ROOT, ROOT_ID,
    bindings, clean, rational, eq, decode, encode, terms, current, state_encode)
from independent_source_gauge_legendre import realify, matrix_coordinates
from independent_source_coframe_live_ordering import FREE
from source_spatial_active_phase_splice import dm, DOMAIN
from source_full_gauss_section import SourceFullGaussSection


def zero(value): assert s.cancel(s.expand(value)) == 0

def pack(forms):
    return dm(s.SparseMatrix(len(forms),112*112,{(k,112*i+j):v
        for k,H in enumerate(forms)for(i,j),v in rational(H).todok().items()}))


def unpack_row(matrix,row):
    return s.SparseMatrix(112,112,{(j//112,j%112):DOMAIN.to_sympy(v)
        for j,v in matrix.rep.get(row,{}).items()if v})


class RawFullSection:
    def __init__(self):
        self.old=RawGaussSection();n=self.old.native;self.native=n
        self.W=n.B.row_join(n.S)
        combine=lambda Ms,w:rational(sum((v*Ms[j]for j,v in enumerate(w)),s.zeros(*Ms[0].shape)))
        self.K=[combine(n.fund,self.W[:,a])for a in range(12)]
        self.scalar=[combine(n.rho,self.W[:,a])for a in range(12)]
        self.ad=[combine(n.ad,self.W[:,a])for a in range(12)]
        self.L=[s.diag(s.zeros(6),rho,ad,ad,ad)for rho,ad in zip(self.scalar,self.ad)]
        complex_matter=[combine(n.matter,self.W[:,a])for a in range(12)]
        self.R=[s.diag(M,M.conjugate())for M in complex_matter]
        self.structure=[rational(self.W.inv()*ad*self.W)for ad in self.ad]
        for a in range(12):
            eq(self.K[a].H,-self.K[a]);eq(self.R[a].H,-self.R[a])
            zero(s.trace(self.L[a]));zero(s.trace(self.structure[a]))
            for b in range(12):
                weights=self.structure[a][:,b]
                eq(self.K[a]*self.K[b]-self.K[b]*self.K[a],combine(self.K,weights))
                eq(self.scalar[a]*self.scalar[b]-self.scalar[b]*self.scalar[a],combine(self.scalar,weights))
                small=[M[:63,:63]for M in complex_matter]
                eq(small[a]*small[b]-small[b]*small[a],combine(small,weights))
        gauge_fixed=[j-67 for j in self.old.fixed]
        self.gauge_free=[j for j in range(36)if j not in gauge_fixed]
        self.gauge_embedding=s.eye(36)[:,self.gauge_free]
        self.E=s.diag(s.eye(6),n.R,self.gauge_embedding)
        self.read=s.diag(s.eye(6),n.Rd.T,self.gauge_embedding.T)
        self.C=s.zeros(12,112);self.C[:9,6:76]=n.O.T
        for j,pivot in enumerate(gauge_fixed):self.C[9+j,76+pivot]=1
        eq(self.C*self.E,s.zeros(12,100));eq(self.read*self.E,s.eye(100))
        self.b0=s.Matrix.vstack(self.old.source[:6,:],n.v,self.old.source[67:,:])
        self.z0=s.Matrix.vstack(self.b0[:6,:],s.zeros(61,1),self.gauge_embedding.T*self.b0[76:,:])
        self.offset=self.b0-self.E*self.z0
        self.normal=self.C.T*(self.C*self.C.T).inv()
        frame=self.normal.row_join(self.E)
        eq(self.C.col_join(self.read)*frame,s.eye(112));eq(frame*self.C.col_join(self.read),s.eye(112))
        self.frame_det=s.factor(DOMAIN.to_sympy(dm(frame).det()))
        self.cache={}

    def chart(self,point):
        key=tuple(point)
        if key in self.cache:return self.cache[key]
        base=self.offset+self.E*point
        eq(self.C*(base-self.b0),s.zeros(12,1))
        V=rational(s.Matrix.hstack(*(L*base for L in self.L)))
        M=rational(self.C*V)
        alpha,free=M.gauss_jordan_solve(self.C);assert free.rows==0
        alpha=rational(alpha);tangent=s.eye(112)-V*alpha
        z=rational(self.read*tangent)
        first=alpha.col_join(z);forward=V.row_join(self.E)
        eq(first*forward,s.eye(112));eq(forward*first,s.eye(112))
        # Differentiate exp(-alpha.L)b before solving the original slice
        # constraints. This is the inverse-map equation rather than a
        # negated forward-curvature formula.
        raw=[s.MutableSparseMatrix(112,112,{})for _ in range(112)]
        for a,La in enumerate(self.L):
            for k in range(112):
                row=La[k,:]
                if row.todok():raw[k]-=row.T*alpha[a,:]+alpha[a,:].T*row
            for b in range(a,12):
                acceleration=rational((La*self.L[b]+self.L[b]*La)*base/2)
                outer=alpha[a,:].T*alpha[b,:]
                if a!=b:outer+=alpha[b,:].T*alpha[a,:]
                for(k,_),v in acceleration.todok().items():raw[k]+=v*outer
        raw=pack(raw)
        Ha=dm(M.inv()*self.C)*raw
        zero_h=dm(self.C)*raw-dm(M)*Ha
        assert zero_h.is_zero_matrix
        Hz=dm(self.read)*(raw-dm(V)*Ha)
        second=DM.vstack(Ha,Hz)
        result={'base':base,'V':V,'M':M,'alpha':alpha,'z':z,'first':first,'forward':forward,
                'second':second,'Ha':[unpack_row(Ha,a)for a in range(12)],'Hz':[unpack_row(Hz,j)for j in range(100)]}
        self.cache[key]=result
        return result

    def extend(self,point,value,gradient,Hessian):
        c=self.chart(point);out={}
        def add(vector,f=0,g=None,H=None):
            for word,coefficient in vector.items():
                record=out.setdefault(word,[s.S.Zero,s.zeros(112,1),s.zeros(112)])
                record[0]+=coefficient*f
                if g is not None:record[1]+=coefficient*g
                if H is not None:record[2]+=coefficient*H
        for word in set(value)|set(gradient)|set(Hessian):
            df=gradient.get(word,s.zeros(100,1));ddf=Hessian.get(word,s.zeros(100))
            g=c['z'].T*df
            H=c['z'].T*ddf*c['z']+sum((df[j]*c['Hz'][j]for j in range(100)if df[j]),s.zeros(112))
            add({word:1},value.get(word,0),g,H)
            for a in range(12):
                add(current(self.R[a],{word:1}),H=c['alpha'][a,:].T*g.T+g*c['alpha'][a,:])
        for a in range(12):
            add(current(self.R[a],value),g=c['alpha'][a,:].T,H=c['Ha'][a])
            for b in range(12):
                ab=current(self.R[a],current(self.R[b],value))
                ba=current(self.R[b],current(self.R[a],value))
                add(terms([(s.Rational(1,2),ab),(s.Rational(1,2),ba)]),H=c['alpha'][a,:].T*c['alpha'][b,:])
        result={w:(s.cancel(f),rational(g),rational(H))for w,(f,g,H)in out.items()}
        for word,(f,g,H)in result.items():
            zero(f-value.get(word,0));eq(self.E.T*g,gradient.get(word,s.zeros(100,1)))
            eq(self.E.T*H*self.E,Hessian.get(word,s.zeros(100)));eq(H,H.T)
        return result

    def gauss(self,point,jets):
        c=self.chart(point);values={w:f for w,(f,_,_)in jets.items()if f}
        for a in range(12):
            v=c['V'][:,a]
            directional={w:(g.T*v)[0]for w,(_,g,_)in jets.items()}
            assert terms([(1,directional),(-1,current(self.R[a],values))])=={}
            derivative={w:rational(self.L[a].T*g+H*v)for w,(_,g,H)in jets.items()}
            for word,(_,g,_)in jets.items():
                for target,coefficient in current(self.R[a],{word:1}).items():
                    derivative.setdefault(target,s.zeros(112,1))
                    derivative[target]-=coefficient*g
            for column in derivative.values():eq(column,s.zeros(112,1))
        return {'all12_original_momentum_map_equations':True,'all1344_first_derivative_equations':True}


def geometry_and_jets(model,oracle,candidate):
    mapping={'original_Lie_basis_change':model.W,'slice_embedding':model.E,'slice_retraction':model.read,
        'original_slice_constraints':model.C,'source_offset':model.offset,'source_point112':model.b0,'source_slice_point100':model.z0}
    for key,value in mapping.items():eq(value,decode(candidate[key]))
    z=s.Matrix(s.symbols('z0:100',real=True));b=model.offset+model.E*z
    V=s.Matrix.hstack(*(L*b for L in model.L));M=rational(model.C*V)
    eq(M[:9,9:],s.zeros(9,3))
    generic=candidate['generic_configuration_density'];symbols={str(v):v for v in z}
    eq(M[:9,:9],decode(generic['D9'],symbols));eq(M[9:,9:],decode(generic['residual3_minor'],symbols))
    rho3=-s.factor(M[9:,9:].det());zero(rho3-s.sympify(generic['rho3'],locals=symbols))
    zero(abs(model.frame_det)-s.sympify(generic['density_constant']))
    assert abs(model.frame_det)==s.Rational(1,256)
    native_Gram=model.W.T*model.native.Gram*model.W
    eq(native_Gram,decode(candidate['Haar']['native_metric_Gram']))
    native_factor=s.sqrt(native_Gram.det());assert native_factor==16*s.sqrt(6)
    zero(native_factor-s.sympify(candidate['Haar']['native_metric_factor']))
    haar=s.zeros(12)
    for a in range(12):
        for bidx in range(12):
            first_a=-model.structure[a]/2;first_b=-model.structure[bidx]/2
            mixed=(model.structure[a]*model.structure[bidx]+model.structure[bidx]*model.structure[a])/6
            haar[a,bidx]=s.trace(mixed)+s.trace(first_a)*s.trace(first_b)-s.trace(first_a*first_b)
    eq(haar,decode(candidate['Haar']['source_coordinate_Haar_Hessian']))
    word=(32,);g=s.Matrix([s.Rational(j%7-3,59)for j in range(100)])
    v=s.Matrix([s.Rational(j%5-2,61)for j in range(100)]);H=v*v.T-s.eye(100)
    live=decode(generic['actual_nonzero_point']);records=[]
    for point in (model.z0,live):
        c=model.chart(point);target=oracle.chart(point)
        eq(c['first'],target.inverse)
        if point==model.z0:
            for key,value in (('source_orbit',c['V']),('source_minor',c['M']),('source_forward_first_jet',c['forward']),('source_inverse_first_jet',c['first'])):
                eq(value,decode(candidate[key]))
        assert (c['second']-target.inverse_second).is_zero_matrix
        assert sum(len(row)for row in c['second'].rep.values())>0
        det=s.factor(DOMAIN.to_sympy(dm(c['forward']).det()))
        density=abs(model.frame_det*c['M'][:9,:9].det()*c['M'][9:,9:].det())
        zero(abs(det)-density)
        jets=model.extend(point,{word:1},{word:g},{word:H})
        result=model.gauss(point,jets)
        expected=oracle.extend_jet({word:1},{word:g},{word:H},point)
        assert set(jets)==set(expected)
        for w,(f,df,d2f)in jets.items():
            zero(f-expected[w]['value']);eq(df,expected[w]['gradient']);eq(d2f,expected[w]['Hessian'])
        records.append({**result,'complete_inverse_twojet_nonzero_entries':sum(len(row)for row in c['second'].rep.values()),
            'forward_Jacobian':str(det),'geometric_configuration_density':str(density),'actual_CAR_twojet_words':len(jets)})
    zero(s.sympify(records[0]['forward_Jacobian'])-s.sympify(candidate['source_forward_determinant']))
    zero(s.sympify(records[0]['geometric_configuration_density'])-s.sympify(generic['source_coordinate_density']))
    zero(s.sympify(records[0]['geometric_configuration_density'])/native_factor-s.sympify(candidate['Haar']['source_density_relative_to_native_metric']))
    zero((model.native.R.T*model.native.R).det()-s.sympify(generic['scalar_R_Gram_determinant']))
    zero((model.native.O.T*model.native.O).det()-s.sympify(generic['scalar_Gram_determinant']))
    zero(abs(model.frame_det)*(model.native.O.T*model.native.O).det()-abs(s.sympify(generic['full_constant_frame_determinant'])))
    assert records[0]['complete_inverse_twojet_nonzero_entries']==candidate['source_inverse_second_nonzero_entries']
    zero(s.sympify(records[1]['geometric_configuration_density'])-s.sympify(generic['actual_coordinate_density']))
    assert records[0]['geometric_configuration_density']!=records[1]['geometric_configuration_density']
    return {'full112_source_group_representation_and_Lie_brackets':True,'shared100_slice_embedding_and_retraction':True,
        'inverse_twojet_method':'Implicit differentiation of C exp(-alpha.L)b=C b_source; full112 by12544 comparison to the candidate outputs.',
        'actual_source_and_live_Gauss_consumers':records,'source_nonorthogonal_frame_factor':str(abs(model.frame_det)),
        'generic_configuration_density':'abs(det D9)*rho3/256 on the source-connected positive chart',
        'native_metric_Haar_factor':str(native_factor),'Maurer_Cartan_determinant_second_variation_checked':True}


def finite_group(model):
    def cayley(T,d):
        X=T/d;return rational((s.eye(7)-X).inv()*(s.eye(7)+X))
    g=cayley(model.native.fund[2],13);h=cayley(model.native.fund[11],17)
    def images(element):
        eq(element.H*element,s.eye(7));zero(element.det()-1)
        internal=s.diag(*(compound(element,d)for d in (6,2,4)))
        matter=s.kronecker_product(s.eye(4),internal);CAR=s.diag(matter,matter.conjugate())
        scalar=realify(compound(element,4))
        ad=s.Matrix.hstack(*(matrix_coordinates(element*T*element.H)for T in model.native.fund))
        boson=s.diag(s.eye(6),scalar,ad,ad,ad)
        eq(CAR.H*CAR,s.eye(504));zero(ad.det()-1);zero(scalar.det()-1)
        return boson,CAR
    Bg,Ug=images(g);Bh,Uh=images(h);Bgh,Ugh=images(g*h)
    eq(Bg*Bh,Bgh);eq(Ug*Uh,Ugh)
    image=finite_wedge(Ugh,(32,))
    zero(sum(s.conjugate(v)*v for v in image.values())-1)
    return {'actual_broken_and_central_native_group_product':True,'whole112_boson_group_volume_one':True,
        'all504_CAR_group_unitarity_and_composition':True,'actual_charged_CAR_image':state_encode(image),
        'full_group_is_kinematic_here':True}


def second_class(model,point,saved):
    c=model.chart(point);D=c['M'][:9,:9];gram=model.native.O.T*model.native.O
    G=s.Matrix(s.symbols('actual_G0:12',real=True));symbols={str(v):v for v in G}
    K=s.Matrix(9,9,lambda a,b:sum(model.structure[a][h,b]*G[h]for h in range(12)))
    eq(K,-K.T);eq(K,decode(saved['actual_broken_Gauss_bracket'],symbols))
    assert K.subs(dict.fromkeys(G[:9,0],0)).todok()
    Delta=s.zeros(9).row_join(D).col_join((-D.T).row_join(K))
    # Direct solution of D*v=f and -D^T*u+K*v=g gives all18 columns.
    Di=D.inv();inverse=(Di.T*K*Di).row_join(-Di.T).col_join(Di.row_join(s.zeros(9)))
    eq(Delta*inverse,s.eye(18));eq(inverse*Delta,s.eye(18))
    eq(Delta,decode(saved['Dirac_matrix'],symbols));eq(inverse,decode(saved['Dirac_inverse'],symbols))
    J=s.zeros(9).row_join(s.eye(9)).col_join((-s.eye(9)).row_join(s.zeros(9)))
    canonical=s.diag(D,D.T)*J
    shear=s.eye(18);shear[:9,9:]=-Di.T*K
    eq(canonical*shear,Delta);zero(shear.det()-1);zero(J.det()-1)
    eq(D,decode(saved['D9']))
    detD=s.factor(D.det());zero(detD-s.sympify(saved['D9_determinant']))
    zero(detD**2-s.sympify(saved['Dirac_determinant']))
    zero(abs(detD)-s.sympify(saved['sqrt_abs_Dirac_determinant']))
    zero(gram.det()-s.sympify(saved['normal_constraint_Jacobian']))
    frame=model.native.R.row_join(model.native.O)
    dual=model.native.Rd.row_join(model.native.O*gram.inv())
    eq(frame.T*dual,s.eye(70));eq(dual*frame.T,s.eye(70))
    normal_momentum=D.T*gram.inv()
    eq(normal_momentum,decode(saved['normal_Gauss_momentum_Jacobian']))
    measure=s.simplify(abs(detD)/(abs(gram.det())*abs(normal_momentum.det())))
    assert measure==1 and saved['measure_cancellation']=='1'
    return {'broken9_Determinant':str(detD),'full_off_level_bracket_keeps_residual3_currents':True,
        'actual18_Dirac_two_sided_inverse':True,'Dirac_determinant':str(detD**2),
        'original70_scalar_cotangent_frame_Jacobian_one':True,
        'delta_C_delta_Gb_sqrt_Delta_reduced_factor':str(measure)}


def main():
    began=time.monotonic();path=HERE/'source_full_gauss_section.json'
    candidate=json.loads(path.read_text());count=bindings(candidate);assert candidate['root']==ROOT_ID
    model=RawFullSection();oracle=SourceFullGaussSection()
    assert model.native.hashes==candidate['source_sha256']
    geometry=geometry_and_jets(model,oracle,candidate)
    print('PASS original112 native12 group, implicit inverse full twojet, source/live100 CAR sections and all12/1344 Gauss rows',flush=True)
    group=finite_group(model)
    print('PASS full native finite group composition,112 volume and504 CAR unitarity',flush=True)
    live=decode(candidate['generic_configuration_density']['actual_nonzero_point'])
    measure=[second_class(model,point,saved)for point,saved in ((model.z0,candidate['source_second_class_measure']),(live,candidate['live_second_class_measure']))]
    assert measure[0]['broken9_Determinant']!=measure[1]['broken9_Determinant']
    wrong=s.sympify(measure[1]['broken9_Determinant'])/256
    assert wrong!=1
    displaced=model.native.v+model.native.O[:,0]/100
    assert (model.native.O.T*displaced).todok()
    print('PASS original broken18 Dirac block with off-level Gauss bracket; canonical phase determinant cancels exactly',flush=True)
    paths=[Path(__file__),path,HERE/'source_full_gauss_section.py',HERE/'independent_source_quantum_gauss_section.py',
        HERE/'independent_source_quantum_stabilizer.py',HERE/'source_scalar_gauss_reduction.json',
        HERE/'source_constraint_preservation.json',HERE/'source_gauss_section_measure.json']
    result={'verdict':'CERTIFIED_NATIVE12_KINEMATIC_SECTION_AND_BROKEN9_SECOND_CLASS_CANONICAL_MEASURE',
        'root':ROOT_ID,'source_sha256':candidate['source_sha256'],
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()for p in paths},
        'source_binding_checks':count,'candidate_used_only_as_complete_jet_comparison_oracle':True,
        'original_geometry':geometry,'finite_original_group':group,'source_and_live_Dirac_measure':measure,
        'incorrect_geometric_factor_on_live_canonical_phase':str(wrong),
        'scope':'Native12 orbit chart and CAR-equivariant twojets are kinematic. Broken9 are original second-class constraints with no residual D9 phase-measure factor; only the stabilizer3 is the remaining physical group quotient.',
        'fixed_source_potential_torque_off_slice_nonzero':True,
        'full_Hamiltonian_equivariance_or_full12_first_class_physical_states_claimed':False,
        'original_residual3_rho_authority_replaced':False,'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds':round(time.monotonic()-began,3)}
    (HERE/'independent_source_full_gauss_section.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS independent full native Gauss section and physical measure',result['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
