#!/usr/bin/env python3
"""Whole native12 orbit coordinates and the original broken9 Dirac measure.

The112-dimensional configuration orbit has a genuine100-dimensional local
slice and an exact CAR-valued inverse two-jet. Its configuration Jacobian
and the physical second-class phase measure are different consumers: the
latter cancels the broken9 determinant. No full12 first-class symmetry of
the fixed-source potential is assumed.
"""
from __future__ import annotations

from functools import lru_cache
import hashlib
import json
import time
import sympy as s
from sympy.polys.matrices import DomainMatrix as DM

from dynamic import HERE,ROOT,ROOT_ID,decode
from retained_hamiltonian_reduction import DOMAIN
from source_spatial_active_phase_splice import dm
from source_quantum_stabilizer import SourceQuantumStabilizer
from source_quantum_gauss_section import exterior,exterior_word,state_clean
from source_stabilizer_phase_reduction import block_diagonal
from source_gauge_legendre import realify
from source_coframe_legendre import rational
from source_lorentz_contact import clean,equal,encode
from source_gauss_quantum_current import apply_superposition,weighted_sum,encode_state


def zero(A):equal(rational(A),s.zeros(*A.shape))


def sparse_domain(A):
    return s.SparseMatrix(*A.shape,{(i,j):DOMAIN.to_sympy(value)
        for i,row in A.rep.items()for j,value in row.items()if value})


class FullGaussChart:
    """All inverse first/second jets at an actual point of the source slice."""
    def __init__(self,model,point):
        self.model=model;self.point=s.Matrix(point)
        assert self.point.shape==(100,1)
        self.base=clean(model.offset+model.embedding*self.point)
        self.orbit=clean(s.Matrix.hstack(*(L*self.base for L in model.L)))
        self.minor=clean(model.constraint*self.orbit)
        assert self.minor.det()!=0
        self.alpha=rational(self.minor.inv()*model.constraint)
        self.z=rational(model.retraction*(s.eye(112)-self.orbit*self.alpha))
        self.forward=self.orbit.row_join(model.embedding)
        self.inverse=self.alpha.col_join(self.z)
        equal(clean(self.forward*self.inverse),s.eye(112))
        equal(clean(self.inverse*self.forward),s.eye(112))
        curvature=[s.MutableSparseMatrix(112,112,{})for _ in range(112)]
        # The first-kind exponential has symmetric second generator product.
        for a in range(12):
            row=self.alpha[a,:]
            mixed=clean(model.L[a]*model.embedding*self.z)
            for k in range(112):
                if mixed[k,:].todok():
                    curvature[k]+=row.T*mixed[k,:]+mixed[k,:].T*row
            for b in range(a,12):
                acceleration=clean((model.L[a]*model.L[b]+model.L[b]*model.L[a])*self.base/2)
                outer=row.T*self.alpha[b,:]
                if b!=a:outer+=self.alpha[b,:].T*row
                for (k,_),coefficient in acceleration.todok().items():
                    curvature[k]+=coefficient*outer
        packed=s.SparseMatrix(112,112*112,{(k,112*i+j):value
            for k,H in enumerate(curvature)for(i,j),value in rational(H).todok().items()})
        self.forward_curvature=dm(packed)
        self.inverse_second=-(dm(self.inverse)*self.forward_curvature)
        assert (dm(self.forward)*self.inverse_second+self.forward_curvature).is_zero_matrix
        self._hessians={}

    def combine_second(self,weights):
        assert weights.shape==(1,112)
        flat=sparse_domain(dm(weights)*self.inverse_second)
        return s.SparseMatrix(112,112,{(j//112,j%112):v for(_,j),v in flat.todok().items()})

    def inverse_hessian(self,row):
        if row not in self._hessians:
            self._hessians[row]=self.combine_second(s.SparseMatrix(1,112,{(0,row):1}))
        return self._hessians[row]

    @property
    def alpha2(self):return [self.inverse_hessian(a)for a in range(12)]
    @property
    def z2(self):return [self.inverse_hessian(12+j)for j in range(100)]


class SourceFullGaussSection:
    """Same-source native12 geometry; not a new full-H gauge-invariance premise."""
    def __init__(self):
        self.native=SourceQuantumStabilizer();m=self.native;g=m.gauge
        self.W=m.B.row_join(m.S)
        self.scalar=[clean(sum((self.W[a,h]*g.rho70[a]for a in range(12)),s.zeros(70)))for h in range(12)]
        self.ad=[clean(g.ad(self.W[:,h]))for h in range(12)]
        self.L=[block_diagonal(s.zeros(6),T,A,A,A)for T,A in zip(self.scalar,self.ad)]
        self.R=[clean(Q/s.I)for Q in m.Q_b+m.Q_s]
        self.K=[clean(sum((self.W[a,h]*g.fundamental[a]for a in range(12)),s.zeros(7)))for h in range(12)]
        self.structure=[clean(self.W.inv()*A*self.W)for A in self.ad]
        for a in range(12):
            equal(self.K[a].H,-self.K[a]);equal(self.R[a].H,-self.R[a])
            assert s.trace(self.L[a])==0
            for b in range(12):
                expected=sum((self.structure[a][c,b]*self.K[c]for c in range(12)),s.zeros(7))
                equal(clean(self.K[a]*self.K[b]-self.K[b]*self.K[a]),clean(expected))
        saved=json.loads((HERE/'source_stabilizer_phase_reduction.json').read_text())
        self.gauge_pivots=tuple(j-67 for j in saved['slice']['whole_coordinate_pivots'])
        self.gauge_free=tuple(j for j in range(36)if j not in self.gauge_pivots)
        Ip=s.SparseMatrix(36,3,{(row,j):1 for j,row in enumerate(self.gauge_pivots)})
        If=s.SparseMatrix(36,33,{(row,j):1 for j,row in enumerate(self.gauge_free)})
        self.embedding=block_diagonal(s.eye(6),m.graph.R,If)
        self.retraction=block_diagonal(s.eye(6),m.graph.dual_R.T,If.T)
        equal(self.retraction*self.embedding,s.eye(100))
        self.constraint=s.SparseMatrix(12,112,{})
        self.constraint[:9,6:76]=m.graph.O.T
        self.constraint[9:,76:]=Ip.T
        zero(self.constraint*self.embedding)
        normal=s.SparseMatrix(112,12,{})
        normal[6:76,:9]=m.graph.O;normal[76:,9:]=Ip
        self.normal=normal
        self.frame=normal.row_join(self.embedding)
        self.normalized_constraint=block_diagonal(m.c.gram.inv(),s.eye(3))*self.constraint
        equal(self.normalized_constraint.col_join(self.retraction)*self.frame,s.eye(112))
        equal(self.frame*self.normalized_constraint.col_join(self.retraction),s.eye(112))
        self.frame_determinant=s.simplify(DOMAIN.to_sympy(dm(self.frame).det()))
        bg=m.graph.common.scalar.exchange.active['actual_background']
        self.e0=s.Matrix(bg['coframe']).applyfunc(s.sympify)
        self.A0=s.Matrix(bg['gauge_connection']).applyfunc(s.sympify)[1:,:]
        q=s.Matrix([self.e0[j]for j in(5,9,10,13,14,15)])
        self.b0=s.Matrix.vstack(q,m.c.vacuum,self.A0.reshape(36,1))
        self.z0=s.Matrix.vstack(q,s.zeros(61,1),If.T*self.A0.reshape(36,1))
        self.offset=clean(self.b0-self.embedding*self.z0)
        self.coordinates=s.Matrix(s.symbols('z0:100',real=True))
        self.slice_field=clean(self.offset+self.embedding*self.coordinates)
        self.generic_orbit=clean(s.Matrix.hstack(*(L*self.slice_field for L in self.L)))
        self.generic_minor=clean(self.constraint*self.generic_orbit)
        self.D9=self.generic_minor[:9,:9]
        zero(self.generic_minor[:9,9:])
        self.M3=self.generic_minor[9:,9:]
        self.rho3=-s.factor(self.M3.det())
        old_a=self.gauge_free.index(1)+67
        old_b=self.gauge_free.index(12)+67
        assert s.expand(self.rho3-8*self.coordinates[old_a]**2*self.coordinates[old_b])==0
        D_original=m.c.select.T*m.c.consistency_matrix(self.slice_field[6:76,:])*m.c.select
        equal(self.D9,D_original)
        transformed=clean(self.normalized_constraint.col_join(self.retraction)*self.generic_orbit.row_join(self.embedding))
        zero(transformed[:12,12:]);equal(transformed[12:,12:],s.eye(100))
        equal(transformed[:12,:12],block_diagonal(m.c.gram.inv(),s.eye(3))*self.generic_minor)
        self.density_constant=s.simplify(abs(self.frame_determinant)/m.c.gram.det())
        self.native_metric=clean(self.W.T*g.gram*self.W)
        self.metric_Haar_factor=s.sqrt(s.factor(self.native_metric.det()))
        assert self.metric_Haar_factor>0
        self.haar_hessian=s.Matrix(12,12,lambda a,b:s.trace(self.structure[a]*self.structure[b])/12)
        self._charts={}
        self.source=self.chart(self.z0)

    def chart(self,point=None):
        point=self.z0 if point is None else s.Matrix(point)
        key=tuple(point)
        if key not in self._charts:self._charts[key]=FullGaussChart(self,point)
        return self._charts[key]

    def extend_jet(self,value,gradient,Hessian,point=None):
        c=self.chart(point);result={}
        def add(vector,v=0,g=None,H=None):
            for word,coefficient in vector.items():
                item=result.setdefault(word,{'value':s.S.Zero,'gradient':s.zeros(112,1),'Hessian':s.zeros(112)})
                item['value']+=coefficient*v
                if g is not None:item['gradient']+=coefficient*g
                if H is not None:item['Hessian']+=coefficient*H
        for word in set(value)|set(gradient)|set(Hessian):
            first=gradient.get(word,s.zeros(100,1));second=Hessian.get(word,s.zeros(100))
            full_first=c.z.T*first
            weights=s.zeros(1,112);weights[0,12:]=first.T
            full_second=c.z.T*second*c.z+c.combine_second(weights)
            add({word:1},value.get(word,0),full_first,full_second)
            for a in range(12):
                image=apply_superposition(self.R[a],{word:1})
                if image:
                    mixed=c.alpha[a,:].T*full_first.T+full_first*c.alpha[a,:]
                    add(image,H=mixed)
        for a in range(12):
            image=apply_superposition(self.R[a],value)
            if image:add(image,g=c.alpha[a,:].T,H=c.inverse_hessian(a))
            for b in range(a,12):
                ab=apply_superposition(self.R[a],apply_superposition(self.R[b],value))
                if a==b:
                    if ab:add(ab,H=c.alpha[a,:].T*c.alpha[b,:])
                else:
                    ba=apply_superposition(self.R[b],apply_superposition(self.R[a],value))
                    sym=weighted_sum([(s.Rational(1,2),ab),(s.Rational(1,2),ba)])
                    if sym:add(sym,H=c.alpha[a,:].T*c.alpha[b,:]+c.alpha[b,:].T*c.alpha[a,:])
        for item in result.values():
            item['value']=s.cancel(item['value'])
            item['gradient']=rational(item['gradient']);item['Hessian']=rational(item['Hessian'])
            equal(item['Hessian'].T,item['Hessian'])
        return result

    def verify_Gauss_jet(self,jet,point=None):
        c=self.chart(point);value={w:j['value']for w,j in jet.items()if j['value']}
        for a in range(12):
            residual={w:-s.I*(c.orbit[:,a].T*j['gradient'])[0]for w,j in jet.items()}
            residual=weighted_sum([(1,residual),(s.I,apply_superposition(self.R[a],value))])
            assert state_clean(residual)=={}
            derivatives={w:clean(-s.I*(self.L[a].T*j['gradient']+j['Hessian']*c.orbit[:,a]))for w,j in jet.items()}
            for w,j in jet.items():
                for out,coefficient in apply_superposition(self.R[a],{w:1}).items():
                    derivatives.setdefault(out,s.zeros(112,1))
                    derivatives[out]+=s.I*coefficient*j['gradient']
            for derivative in derivatives.values():zero(derivative)
        return {'all12_geometric_Gauss_values_zero':True,'all1344_first_Gauss_derivatives_zero':True,
                'whole112_gradient_and112_by112_Hessian_retained':True}

    def matter_group(self,g):
        from source_gauge_legendre import source
        _,_,degrees,_=source.parse_source(ROOT)
        internal=block_diagonal(*(exterior(g,k)for k in degrees))
        rho=block_diagonal(*([internal]*4))
        return block_diagonal(rho,rho.conjugate())

    def boson_group(self,g):
        gauge=self.native.gauge
        scalar=realify(exterior(g,4))
        ad=s.Matrix(12,12,lambda a,b:gauge.native_pair(gauge.fundamental[a],g*gauge.fundamental[b]*g.H))
        ad=clean(gauge.gram_inverse*ad)
        return block_diagonal(s.eye(6),scalar,ad,ad,ad)

    def second_class_data(self,point=None):
        c=self.chart(point);phi=c.base[6:76,:]
        D=clean(self.native.graph.O.T*s.Matrix.hstack(*(T*phi for T in self.scalar[:9])))
        currents=s.Matrix(s.symbols('actual_G0:12',real=True))
        K=s.Matrix(9,9,lambda a,b:sum(self.structure[a][h,b]*currents[h]for h in range(12)))
        equal(K.T,-K)
        Di=clean(D.inv())
        Delta=s.zeros(9).row_join(D).col_join((-D.T).row_join(K))
        inverse=(Di.T*K*Di).row_join(-Di.T).col_join(Di.row_join(s.zeros(9)))
        equal(clean(Delta*inverse),s.eye(18));equal(clean(inverse*Delta),s.eye(18))
        canonical=s.zeros(9).row_join(D).col_join((-D.T).row_join(s.zeros(9)))
        triangular=s.eye(9).row_join(-Di.T*K).col_join(s.zeros(9).row_join(s.eye(9)))
        equal(clean(canonical*triangular),Delta)
        # The scalar canonical frame is linear; its momentum frame is exactly
        # the inverse transpose, including the original nonorthonormal R.
        R,O=self.native.graph.R,self.native.graph.O
        frame=R.row_join(O);dual=self.native.graph.dual_R.row_join(O*self.native.c.gram.inv())
        equal(frame.T*dual,s.eye(70));equal(dual*frame.T,s.eye(70))
        derivative=clean(D.T*self.native.c.gram.inv())
        detD=s.factor(D.det());gramdet=self.native.c.gram.det()
        assert detD!=0
        cancellation=s.simplify(abs(detD)/(abs(gramdet)*abs(derivative.det())))
        assert cancellation==1
        return {'D9':encode(D),'D9_determinant':str(detD),'actual_broken_Gauss_bracket':encode(K),
            'Dirac_matrix':encode(Delta),'Dirac_inverse':encode(inverse),
            'both_inverse_identities_and_unit_triangular_factor_checked':True,
            'Dirac_determinant':str(detD**2),'sqrt_abs_Dirac_determinant':str(abs(detD)),
            'normal_constraint_Jacobian':str(gramdet),'normal_Gauss_momentum_Jacobian':encode(derivative),
            'measure_cancellation':str(cancellation),
            'canonical_phase_measure':'phi=v+R*x+O*y, Pi_phi=Rdual*pi+O*GramO^-1*pi_y has total scalar phase Jacobian1. C=GramO*y and dGb/dpi_y=D9^T GramO^-1. Integrating delta(C)delta(Gb)sqrt(det Delta) over y,pi_y leaves exactly dx dpi, with no field-dependent D9 factor.',
            'quantum_form_consumer':'The broken9 second-class reduction preserves the original canonical103 phase measure. Its fixed-order scalar operators need their adjoints in that actual measure; the source form sum Pi_j^dagger Pi_j/(2h00) is not justified by inserting the geometric full12 configuration determinant.',
            'remaining_Gs_not_set_zero_in_Dirac_bracket':True}


def main():
    started=time.monotonic();m=SourceFullGaussSection()
    c=m.source
    print('PASS original native12 source orbit, complete112 inverse first/two-jets and100 slice',flush=True)
    det_source=s.simplify(DOMAIN.to_sympy(dm(c.forward).det()))
    D0=c.minor[:9,:9];M0=c.minor[9:,9:]
    assert s.simplify(det_source-m.frame_determinant*D0.det()*M0.det()/m.native.c.gram.det())==0
    rho0=abs(det_source)
    z=m.z0.copy();z[6:67,0]=(m.native.graph.dual_R.T*m.native.c.vacuum)/100
    z[67+m.gauge_free.index(1)]*=s.Rational(101,100)
    actual=m.chart(z)
    actual_det=s.simplify(DOMAIN.to_sympy(dm(actual.forward).det()))
    Da=actual.minor[:9,:9];Ma=actual.minor[9:,9:]
    assert s.simplify(abs(actual_det)-m.density_constant*abs(Da.det())*abs(Ma.det()))==0
    assert Da.det()!=D0.det() and abs(actual_det)!=rho0
    print('PASS generic block Jacobian and exact varying full12 density, with scalar-frame normalization retained',flush=True)
    word=(32,);gradient=s.Matrix([s.Rational(j%7-3,59)for j in range(100)])
    direction=s.Matrix([s.Rational(j%5-2,61)for j in range(100)])
    Hessian=direction*direction.T-s.eye(100)
    outputs=[]
    for point in (None,z):
        jet=m.extend_jet({word:1},{word:gradient},{word:Hessian},point)
        outputs.append(m.verify_Gauss_jet(jet,point))
    print('PASS actual charged fullCAR sections and all12 Gauss/all1344 derivative rows at source and a live source-chart point',flush=True)
    # A finite broken-direction source group element consumes the very same
    # native fundamental action and all exterior/car fields.
    X=m.native.gauge.fundamental[2]/13
    g=clean((s.eye(7)-X).inv()*(s.eye(7)+X))
    equal(g.H*g,s.eye(7));assert s.simplify(g.det())==1
    B=m.boson_group(g);U=m.matter_group(g)
    equal(U.H*U,s.eye(504));assert s.simplify(B.det())==1
    image=exterior_word(U,word)
    assert s.simplify(sum(s.conjugate(v)*v for v in image.values())-1)==0
    first=m.second_class_data();second=m.second_class_data(z)
    print('PASS original18 second-class Dirac inverse and exact generic/actual phase measure cancellation',flush=True)
    names=('source_full_gauss_section.py','source_quantum_stabilizer.py','source_quantum_gauss_section.py',
        'source_stabilizer_phase_reduction.json','source_scalar_gauss_reduction.py','source_scalar_gauss_reduction.json',
        'source_constraint_preservation.py','source_constraint_preservation.json','source_gauge_legendre.py',
        'source_gauss_section_measure.json','source_reducing_coframe_metric.json')
    result={'root':ROOT_ID,'scope':'ORIGINAL_NATIVE12_GEOMETRIC_SECTION_AND_BROKEN9_SECOND_CLASS_CANONICAL_MEASURE',
        'source_sha256':m.native.graph.common.source_hashes,
        'input_sha256':{str((HERE/name).relative_to(ROOT)):hashlib.sha256((HERE/name).read_bytes()).hexdigest()for name in names},
        'coordinate_order':{'ambient112':'q6, original real scalar70, original three spatial native connections36',
            'slice100':'q6, original scalar x61, same original33 free spatial gauge coordinates',
            'Lie12':'native-Gram-orthogonal broken B9 followed by original stabilizer S3'},
        'original_Lie_basis_change':encode(m.W),'slice_embedding':encode(m.embedding),'slice_retraction':encode(m.retraction),
        'original_slice_constraints':encode(m.constraint),'source_offset':encode(m.offset),'source_point112':encode(m.b0),'source_slice_point100':encode(m.z0),
        'source_orbit':encode(c.orbit),'source_minor':encode(c.minor),'source_forward_first_jet':encode(c.forward),
        'source_inverse_first_jet':encode(c.inverse),'source_forward_determinant':str(det_source),
        'second_jet':'All112 forward Hessians are generated from sym(L_a L_b)b and L_a*embedding. inverse_second=-inverse_first*forward_curvature, with the full 112x12544 composition identity checked exactly. The public chart supplies every inverse Hessian or weighted contraction.',
        'source_inverse_second_nonzero_entries':sum(len(row)for row in c.inverse_second.rep.values()),
        'generic_configuration_density':{'D9':encode(m.D9),'residual3_minor':encode(m.M3),'rho3':str(m.rho3),
            'scalar_Gram_determinant':str(m.native.c.gram.det()),'scalar_R_Gram_determinant':str((m.native.graph.R.T*m.native.graph.R).det()),
            'full_constant_frame_determinant':str(m.frame_determinant),'density_constant':str(m.density_constant),
            'rho12':'density_constant*abs(det D9(phi))*rho3 on the source-connected positive chart',
            'source_coordinate_density':str(rho0),'actual_nonzero_point':encode(z),'actual_coordinate_density':str(abs(actual_det)),
            'geometric_not_physical_first_class_replacement':True},
        'Haar':{'native_metric_Gram':encode(m.native_metric),'native_metric_factor':str(m.metric_Haar_factor),
            'coordinate_identity_density':1,'source_density_relative_to_native_metric':str(s.simplify(rho0/m.metric_Haar_factor)),
            'first_kind_coordinate_Haar':'det(sum_{n>=0}(-ad_X)^n/(n+1)!), X=sum alpha_a K_a; positive near0 with density1. This is the original left Maurer-Cartan Jacobian, not probability Haar.',
            'source_coordinate_Haar_Hessian':encode(m.haar_hessian),
            'whole_field_trace_zero_and_finite_group_volume_preservation':True,'all504_finite_CAR_unitarity_checked':True},
        'actual_C2_Gauss_consumers':outputs,'source_second_class_measure':first,'live_second_class_measure':second,
        'scope_separation':'The full12 coordinate orbit and CAR equivariant extension are a local kinematic producer for original kinetic calculations. The fixed-source potential has nonzero broken9 torque away from C=0, so full-H gauge-equivariance and a12-first-class physical quotient are not asserted. The actual second-class Dirac integration cancels D9; its physical canonical measure retains the existing residual3 rho consumer.',
        'public_API':'SourceFullGaussSection.chart(point100=None), extend_jet(value,gradient100,Hessian100,point=None), verify_Gauss_jet(jet,point=None), second_class_data(point=None). Each chart exposes base,orbit,minor,alpha,z, inverse_hessian(row), alpha2,z2 and combine_second(weights112).',
        'old_scalar_ordering_equals_original_full_group_Laplacian_assumed':False,
        'new_source_occurrence_or_proper_clock_change':False,'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'source_full_gauss_section.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS complete native Gauss section and physical Dirac measure',result['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
