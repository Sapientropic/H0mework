#!/usr/bin/env python3
"""First canonical subprincipal clock generated from the original full form.

The principal clock is scalar on full CAR. The original inner graph therefore
cancels its first Jordan/Moyal contribution; the actual force Jacobian then
generates the order-minus-one clock. Original Y is retained at momentum order
zero and first enters the clock at order minus two.
"""
from __future__ import annotations

import hashlib
import json
import time
from types import SimpleNamespace
import sympy as s

from dynamic import HERE, ROOT, ROOT_ID, decode
from source_canonical_star_temporal_reduction import bound
from source_principal_clock_cone import SourcePrincipalClockCone
from source_scalar_weyl_symbol import SourceScalarWeylSymbol
from source_common_weyl_symbol import gauge_coefficients
from source_temporal_coframe_pairing import generic_pairing
from source_reducing_coframe_metric import complete_coefficients
from source_quantum_ordered_temporal import OrderedTemporalCoefficients
from source_quantum_temporal_symbol import N, SYM
from source_coframe_legendre import rational
from source_lorentz_contact import equal, encode
from source_coframe_live_ordering import full
from source_full_quantum_adjoint import split_matter
from source_gauss_quantum_current import apply_superposition, weighted_sum, encode_state
from source_quantum_grade_structure import matrix_grade, state_grade


def zero(x): assert s.factor(s.cancel(x))==0


def jet_inner_graph():
    """Literal eta/pi contraction including the mixed canonical contraction."""
    C,X,Cz,Cp,Xz,Xp=s.symbols('C X Cz Cp Xz Xp',commutative=False)
    eps=s.Symbol('inverse_cotangent_scale',real=True)
    PB=lambda a,b,c,d:a*d-b*c
    # At eta=pi=0, G=-pi*C and F=F0+eta*X. The last terms are
    # the tensor product of the exact primary and first canonical contractions.
    projected_GF=s.I*C*X/2-eps*PB(Cz,Cp,Xz,Xp)/4
    projected_FG=-s.I*X*C/2+eps*PB(Xz,Xp,Cz,Cp)/4
    projected=s.expand((projected_GF-projected_FG)/s.I)
    jordan=(C*X+X*C)/2+eps*s.I*(PB(Cz,Cp,Xz,Xp)+PB(Xz,Xp,Cz,Cp))/4
    assert s.expand(projected-jordan)==0
    # This is an arbitrary matrix entry and arbitrary canonical pair, not a
    # claim that the thirteen compressed time coefficients commute.
    cz,cp=s.symbols('scalar_Cz scalar_Cp',real=True)
    assert s.expand((PB(Cz,Cp,Xz,Xp)+PB(Xz,Xp,Cz,Cp)).subs({Cz:cz,Cp:cp}))==0
    return {'original_generator':'G=-sum_a pi_a*(C_a-c_a)',
        'literal_projected_inner_action':str(projected),
        'projected_identity':'eval_primary0 [G,F]_star/i = (C star partial_eta(F)+partial_eta(F) star C)/2',
        'mixed_primary_canonical_contractions_retained':True,
        'all100_canonical_pairs':'The displayed identity holds entrywise for each canonical pair and is summed over the original (z100,p100). Scalar principal C0 makes each first Poisson anticommutator zero; no canonical derivative is frozen.',
        'ordered_cone_composition':'Each leading Jordan map is multiplication by its scalar clock and has zero first canonical correction. Its Sylvester inverse has the reciprocal leading multiplication and zero first correction. All original ordered R/J compositions consequently have zero first Moyal contribution.',
        'primary_ideal':'The generator has primary-momentum degree one and no eta dependence; its commutator preserves the positive-primary ideal even with canonical star products.',
        'noncommuting_original_atoms':'No Poisson bracket among A0_2 and trace(S2) is set to zero; their previously generated nonzero canonical bracket remains.'}


def operator_pair(identity=0,current=None):
    return {'identity':s.factor(identity),'current':s.SparseMatrix(s.zeros(504) if current is None else rational(current))}


def combination(coefficients,operators):
    return operator_pair(sum(c*o['identity'] for c,o in zip(coefficients,operators)),
        sum((c*o['current'] for c,o in zip(coefficients,operators)),s.zeros(504)))


def encode_pair(op): return {'identity':str(op['identity']),'current504':encode(op['current'])}


def apply_pair(op,state):
    return weighted_sum([(op['identity'],state),(1,apply_superposition(op['current'],state))])


class SourceClockSubprincipal:
    def __init__(self):
        self.cone=SourcePrincipalClockCone(); self.factors=self.cone.source_factors()
        self.p,self.witness=self.cone.actual_covector(self.factors)
        self.weyl=SourceScalarWeylSymbol(); m=self.weyl; f=self.factors
        self.y=m.temporal.family.y
        self.scalar=m.coefficients(self.y,f['q'],f['x'],f['A'])
        self.gauge=gauge_coefficients(m,self.scalar)
        equal(self.scalar['a'],f['scalar_factor70x100'][:,6:])
        equal(self.gauge['a'],f['gauge_factor36x100'][:,6:])
        metric=complete_coefficients(SimpleNamespace(section=m.section))
        self.pairing=generic_pairing(SimpleNamespace(coframe=m.native.joint.coframe,metric=metric),m.temporal.family)
        sub=dict(zip(m.native.joint.coframe.q,f['q']))
        cf_current=full(rational(sum((M*self.p[j] for j,M in enumerate(self.pairing['Mh'])),s.zeros(8)).subs(sub)))
        # The chosen covector is radial in the coframe block; the original
        # Hermitian coframe current has zero radial contraction.
        equal(cf_current,s.zeros(504))
        def symbol_linear(data):
            p=self.p[6:,:]
            identity=s.factor((p.T*data['momentum_identity'])[0])
            coefficients=rational(p.T*data['momentum_current'])
            return operator_pair(identity,sum((coefficients[a]*m.charges[a] for a in range(12)),s.zeros(504)))
        self.scalar1=symbol_linear(self.scalar)
        self.gauge1=symbol_linear(self.gauge)
        self.coframe1=operator_pair(0,cf_current)
        self.H1=combination([1,1,1],[self.coframe1,self.scalar1,self.gauge1])
        self.nongauge1=combination([1,1],[self.coframe1,self.scalar1])
        self.atoms=[]
        for y in self.y:
            self.atoms.append(operator_pair(s.diff(self.nongauge1['identity'],y),self.nongauge1['current'].diff(y)))
        # Source-generated electric momentum and residual current are the two
        # factors of the degree-one electric Gram. No static-CAR replacement.
        Pi=rational(self.gauge['a']*self.p[6:,:]).reshape(3,12)
        current_rows=self.gauge['current']
        G=self.factors['native_inverse_Gram'];L=f['L'];Li=L.inv();v=f['volume']
        S1=[]
        for a in range(12):
            C=current_rows[:,a].reshape(3,12)
            S1.append(rational(v*Li.T*(Pi*G*C.T+C*G*Pi.T)*Li/2))
        for i,j in SYM:
            self.atoms.append(operator_pair(0,sum((S[i,j]*m.charges[a] for a,S in enumerate(S1)),s.zeros(504))))
        B,_=self.cone.native.gauge.spatial_data(f['data']['connection'],s.zeros(3,48))
        crossed=rational(v*Li.T*(Pi*B.T)*Li)
        self.atoms.extend(operator_pair(c) for c in (crossed[2,1]-crossed[1,2],crossed[0,2]-crossed[2,0],crossed[1,0]-crossed[0,1]))
        assert len(self.atoms)==13
        raw=OrderedTemporalCoefficients(); replace=dict(zip(raw.y,self.y))
        weights=[c.subs(replace,simultaneous=True) for c in raw.coefficients]
        rebuilt=combination(weights,self.atoms)
        zero(rebuilt['identity']-self.H1['identity']);equal(rebuilt['current'],self.H1['current'])
        for atom in self.atoms:
            assert not set(self.y)&(atom['identity'].free_symbols|atom['current'].free_symbols)
            zero(s.im(atom['identity']));equal(atom['current'].H,atom['current']);matrix_grade(atom['current'],0)
        self.weights=weights
        self.source_clock={self.y[0]:N,**dict.fromkeys(self.y[1:],0)}
        self.force=[]
        for y in self.y:
            self.force.append(operator_pair(-s.diff(self.H1['identity'],y).subs(self.source_clock),
                -self.H1['current'].diff(y).subs(self.source_clock)))
        Pi,E,S=self.cone.gram(f,self.p);T=s.trace(S);n=self.y[0];b=s.Matrix(self.y[1:])
        a0=s.factor((self.p.T*f['a0_matrix100']*self.p)[0])
        self.H2=n*a0+(n*n*T-(b.T*S*b)[0])/(2*n*(n*n-(b.T*b)[0]))
        force2=-s.Matrix([s.diff(self.H2,y) for y in self.y])
        equal(rational(force2.subs(self.source_clock)),s.zeros(4,1))
        self.J=rational(force2.jacobian(self.y).subs(self.source_clock)); assert self.J.det()!=0
        Ji=rational(self.J.inv());equal(Ji*self.J,s.eye(4));equal(self.J*Ji,s.eye(4))
        self.clock=[combination(list(-Ji[a,:]),self.force) for a in range(4)]
        for a in range(4):
            residual=combination([1,*list(self.J[a,:])],[self.force[a],*self.clock])
            zero(residual['identity']);equal(residual['current'],s.zeros(504))
            zero(s.im(self.clock[a]['identity']));equal(self.clock[a]['current'].H,self.clock[a]['current'])
            matrix_grade(self.clock[a]['current'],0)
        # Stationarity makes the first reduced energy simply H1 at C0;
        # the term partial_y H2 . C_-1 vanishes by the actual four forces.
        self.energy1=operator_pair(self.H1['identity'].subs(self.source_clock),self.H1['current'].subs(self.source_clock))
        data=self.cone.original.coefficients((N,0,0,0),f['q'],f['x'],f['A'])
        _,self.Y=split_matter(data);matrix_grade(self.Y,1)
        self.Y_force0=operator_pair(0,-self.Y/N)

    def actual_consumer(self):
        word=(144,396);state={word:s.S.One}
        forces=[apply_pair(F,state) for F in self.force]
        clock=[apply_pair(C,state) for C in self.clock]
        for a in range(4):
            residual=weighted_sum([(1,forces[a]),*[(self.J[a,b],clock[b]) for b in range(4)]])
            assert not residual
        assert any(clock)
        for image in clock:state_grade(image,2,0)
        Y=apply_superposition(self.Y,state);assert Y;state_grade(Y,2,1)
        sharp=apply_superposition(self.Y.H,state);assert weighted_sum([(1,Y),(-1,sharp)])
        return {'input_CAR':list(word),'force_order1_images':[encode_state(F) for F in forces],
            'clock_order_minus1_images':[encode_state(C) for C in clock],
            'all4_first_corrected_force_residuals_zero':True,
            'first_reduced_energy_image':encode_state(apply_pair(self.energy1,state)),
            'original_Y_order0_image':encode_state(Y),'original_Y_adjoint_order0_image':encode_state(sharp),
            'original_Y_first_clock_order':'-2, because the original four forces have order2 and Y has order0',
            'scope':'Symbol fiber on the actual source canonical100 phase chart, realized by compact smooth Gauss sections; not an integrated norm or eigenstate.'}


def main():
    started=time.monotonic()
    names=('source_principal_clock_cone','source_common_weyl_symbol','independent_source_common_weyl_symbol',
        'source_canonical_star_temporal_reduction','independent_source_canonical_star_temporal_reduction',
        'source_temporal_cone_resolvent','independent_source_temporal_cone_resolvent')
    graph=jet_inner_graph()
    m=SourceClockSubprincipal()
    paid={name:bound(name) for name in names}
    principal=paid['source_principal_clock_cone']['actual_source_cotangent_witness']
    equal(m.p,decode(principal['canonical_p100']));equal(m.J,decode(principal['actual_four_force_Jacobian']))
    print('PASS original full canonical Weyl degree-one symbol, all13 atom readback and generated four-clock Jacobian inverse',flush=True)
    actual=m.actual_consumer()
    print('PASS full504 Hermitian grade-zero subprincipal clocks and actual source N2 force residuals; original Y retained at order0',flush=True)
    files=[HERE/(name+'.json') for name in names]+[HERE/name for name in ('source_clock_subprincipal.py',
        'source_principal_clock_cone.py','source_common_weyl_symbol.py','source_scalar_weyl_symbol.py',
        'source_temporal_coframe_pairing.py','source_quantum_ordered_temporal.py','source_full_quantum_adjoint.py')]
    result={'root':ROOT_ID,'scope':'FIRST_SOURCE_GENERATED_CANONICAL_SUBPRINCIPAL_CLOCK_ON_FULL504_CAR',
        'source_sha256':m.cone.native.graph.common.source_hashes,
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'canonical_expansion':'sigma(H)(z,t*p;y)=t^2 H2(z,p;y) Id+t H1(z,p;y)+H0(z;y); C=C0+t^-1 C_-1+O(t^-2)',
        'inner_graph_first_canonical_order':graph,
        'principal_clock':'C0=(sqrt(trace(S2)/(2*a0_2)),0,0,0), generated on the actual nonempty source cone',
        'first_clock_producer':'C_-1=-[partial_y F2(C0)]^-1 F1(C0). The first Jordan/Moyal contribution is zero by the literal original inner graph, not by commuting the original atoms.',
        'actual_canonical_covector':encode(m.p),'actual_force_Jacobian':encode(m.J),
        'all13_original_atom_order1_symbols':[encode_pair(a) for a in m.atoms],
        'original_H1_identity':str(m.H1['identity']),'original_H1_current504':encode(m.H1['current']),
        'four_force_order1_symbols':[encode_pair(F) for F in m.force],
        'four_clock_order_minus1_symbols':[encode_pair(C) for C in m.clock],
        'first_reduced_energy_symbol':encode_pair(m.energy1),
        'original_Y_full504_order0':encode(m.Y),'original_Y_force_order0':encode_pair(m.Y_force0),
        'actual_consumer':actual,
        'lower_order_responsibility':'Order minus two consumes the retained original Y, scalar/coframe/gauge Weyl zero-order corrections, noncommuting products and second canonical Moyal terms. No such term is set to zero here.',
        'complete_quantum_clock_operator_or_spectrum_generated':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED','elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'source_clock_subprincipal.json').write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('PASS source clock subprincipal',result['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
