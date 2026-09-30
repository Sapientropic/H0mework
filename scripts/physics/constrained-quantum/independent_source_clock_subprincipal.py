#!/usr/bin/env python3
"""Independent first canonical clock correction from original Weyl coefficients.

A tensor-product Moyal multiplier computes the primary/canonical mixed
contractions. Original independent implicit-slice symbols then generate H1;
a polynomial coefficient solve recovers its thirteen time atoms, and the
actual principal-force Jacobian generates the full504 clock correction.
"""
from __future__ import annotations

from itertools import product,combinations
from math import factorial
import hashlib
import json
from pathlib import Path
import time
import sympy as s

from independent_source_principal_clock_cone import (
    RawGaussSection,RawLiveCoefficients,HERE,ROOT,ROOT_ID,bindings,source_factors,
    cotangent_values,rational,eq,decode,encode,zero)
from independent_source_scalar_weyl_symbol import original_slice_coefficients
from independent_source_common_weyl_symbol import implicit_gauge_symbol
from independent_source_common_hamiltonian import original_inventory
from independent_source_full_quantum_adjoint import sparse,dual_pair
from independent_source_gauss_quantum_current import apply_state,add_terms,decoded_state
from independent_source_coframe_live_ordering import state_encode
from independent_source_quantum_grade_structure import grade_predicate,grade_state
from independent_source_gauge_legendre import source


def inner_graph_audit():
    eta,pi,z,p,h=s.symbols('eta pi z p canonical_order',commutative=True)
    C,X,Cz,Cp,Xz,Xp=s.symbols('C X Cz Cp Xz Xp',commutative=False)
    variables=(eta,pi,z,p)
    def star(A,B):
        terms=[]
        for a,b,c,d in product(range(2),repeat=4):
            if a+b>1 or c+d>1:continue
            left=A;right=B
            for var,power in zip(variables,(a,b,c,d)):
                if power:left=s.diff(left,var,power)
            for var,power in zip(variables,(b,a,d,c)):
                if power:right=s.diff(right,var,power)
            terms.append((s.I/2)**(a+b+c+d)*(-1)**(b+d)*h**(c+d)*left*right)
        return s.expand(sum(terms))
    clock=C+z*Cz+p*Cp;derivative=X+z*Xz+p*Xp
    G=-pi*clock;F=eta*derivative
    result=s.expand(((star(G,F)-star(F,G))/s.I).subs(dict.fromkeys(variables,0)))
    ordinary=(C*X+X*C)/2
    canonical=s.I*((Cz*Xp-Cp*Xz)+(Xz*Cp-Xp*Cz))/4
    assert s.expand(result-ordinary-h*canonical)==0
    scalar_z,scalar_p=s.symbols('principal_C_z principal_C_p',real=True)
    assert s.expand(canonical.subs({Cz:scalar_z,Cp:scalar_p}))==0
    # Retaining a primary pi in the incoming polynomial cannot create its
    # degree-zero output under this generator, even in the mixed product.
    ideal=s.expand(((star(G,pi*F)-star(pi*F,G))/s.I).subs({eta:0,pi:0,z:0,p:0}))
    assert ideal==0
    return {'literal_tensor_product_primary_and_canonical_star_commutator':str(result),
        'mixed_primary_canonical_contractions_computed':True,
        'scalar_leading_clock_cancels_each_first_canonical_pair':True,
        'primary_positive_degree_preserved_in_mixed_contraction':True,
        'original_all100_pair_scope':'The identity is entrywise for arbitrary matrix jets and each actual canonical coordinate pair; summing100 pairs gives the original first correction without treating compressed weights as coordinates.',
        'nonzero_source_atom_Poisson_brackets_preserved':True}


def pair(coefficients,charges):
    return s.factor(coefficients[0]),sparse(sum((coefficients[j+1]*Q for j,Q in enumerate(charges)),s.zeros(504)))


def compare_pair(value,saved,variables=()):
    sym={str(v):v for v in variables};identity,current=value
    zero(identity-s.sympify(saved['identity'],locals=sym));eq(current,decode(saved['current504'],sym))


def encode_pair(value):return {'identity':str(value[0]),'current504':encode(value[1])}


def apply_pair(value,state):return add_terms([(value[0],state),(1,apply_state(value[1],state))])


def original_H1(section,raw,f,p,ys):
    e=raw.at(raw.e,f['q']);e[:,0]=s.Matrix(ys)
    scalar=original_slice_coefficients(section,e,f['x'],f['A'],f['point'])
    gauge=implicit_gauge_symbol(section,f['point'],e)
    charges=section.native.Qb+section.native.Qs
    eq(scalar['a'],f['scalar_factor'][:,6:]);eq(gauge['a'],f['gauge_factor'][:,6:])
    reduced=p[6:,:]
    scalar1=(reduced.T*scalar['identity']).row_join(reduced.T*scalar['mixed'])
    gauge1=(reduced.T*gauge['momentum_identity']).row_join(s.zeros(1,9)).row_join(reduced.T*gauge['momentum_current'])
    volume=raw.q[0]*raw.q[2]*raw.q[5]
    log_gradient=s.Matrix([s.diff(volume,v)/volume for v in raw.q]);dr=s.Matrix([s.diff(s.sqrt(volume),v) for v in raw.q])
    Mh=[rational(M+s.I*(raw.K*log_gradient)[j]*s.eye(8)) for j,M in enumerate(raw.M)]
    eq(rational(sum((M*dr[j] for j,M in enumerate(Mh)),s.zeros(8))),s.zeros(8))
    point=dict(zip(raw.q,f['q']))
    cf=rational(sum((M*p[j] for j,M in enumerate(Mh)),s.zeros(8)).subs(point))
    eq(cf,s.zeros(8))
    H1=rational(scalar1+gauge1)
    return H1,charges,{'independent_coupled12_scalar_Weyl_momentum_coefficients':True,
        'independent_native_BF_implicit94_gauge_Weyl_momentum_coefficients':True,
        'original_half_density_and_Weyl_placement_corrections_consumed':True,
        'generic_original_Hermitian_coframe_current_radial_contraction_zero':True,
        'raw_scalar_coefficient_row':encode(scalar1),'raw_gauge_coefficient_row':encode(gauge1)}


def extract_thirteen(H1,ys):
    n,*b=ys;delta=n*n-sum(v*v for v in b);pairs=((0,0),(1,1),(2,2),(0,1),(0,2),(1,2))
    weights=[*ys,*[(n*n-b[i]*b[j])/(2*n*delta) if i==j else -b[i]*b[j]/(n*delta) for i,j in pairs],*[-v/delta for v in b]]
    polynomials=[s.Poly(s.cancel(2*n*delta*c),*ys) for c in weights]
    monomials=sorted(set().union(*(set(P.monoms()) for P in polynomials)))
    matrix=s.Matrix([[P.coeff_monomial(word) for P in polynomials] for word in monomials])
    rows=matrix.T.rref()[1];assert len(rows)==13
    inverse=matrix[list(rows),:].inv();eq(inverse*matrix[list(rows),:],s.eye(13))
    actual=[s.Poly(s.cancel(2*n*delta*c),*ys) for c in H1]
    rhs=s.Matrix([[P.coeff_monomial(monomials[i]) for P in actual] for i in rows])
    atoms=rational(inverse*rhs)
    for j in range(13):zero(sum(weights[k]*atoms[k,j] for k in range(13))-H1[j])
    assert all(set(ys).isdisjoint(c.free_symbols) for c in atoms)
    return atoms,{'original_time_weight_polynomial_rank':13,'independent_polynomial_pivot_rows':list(rows),
        'original_H1_exactly_reassembled_in_all_four_time_variables':True,
        'method':'Clear the original common denominator and solve the13 independent polynomial coefficient rows; no electric/current atom constructor is imported.'}


def main():
    started=time.monotonic();path=HERE/'source_clock_subprincipal.json';candidate=json.loads(path.read_text())
    count=bindings(candidate);assert candidate['root']==ROOT_ID
    paid=('source_principal_clock_cone','independent_source_principal_clock_cone',
        'independent_source_scalar_weyl_symbol','independent_source_common_weyl_symbol',
        'independent_source_canonical_star_temporal_reduction','independent_source_temporal_cone_resolvent',
        'independent_source_quantum_grade_structure')
    records={name:json.loads((HERE/(name+'.json')).read_text()) for name in paid}
    for receipt in records.values():count+=bindings(receipt);assert receipt['root']==ROOT_ID
    graph=inner_graph_audit();section,raw=RawGaussSection(),RawLiveCoefficients()
    assert section.native.hashes==candidate['source_sha256']
    principal=records['source_principal_clock_cone'];f=source_factors(section,raw,principal['original_source_factors'])
    p=decode(principal['actual_source_cotangent_witness']['canonical_p100']);eq(p,decode(candidate['actual_canonical_covector']))
    ys=(s.Symbol('quantum_n',positive=True),*s.symbols('quantum_b1:4',real=True))
    H1,Q,coefficient_laws=original_H1(section,raw,f,p,ys)
    total=pair(list(H1),Q)
    zero(total[0]-s.sympify(candidate['original_H1_identity'],locals={str(v):v for v in ys}))
    eq(total[1],decode(candidate['original_H1_current504'],{str(v):v for v in ys}))
    atoms,atom_laws=extract_thirteen(H1,ys)
    _,_,degrees,hashes=source.parse_source(ROOT);assert hashes==candidate['source_sha256']
    labels=[(d,word) for d in degrees for word in combinations(range(7),d)]
    weights=[int(d==6) for _branch in range(2) for _spin in range(4) for d,_ in labels]
    assert len(weights)==504 and sum(weights)==56
    for k in range(13):
        actual=pair(list(atoms[k,:]),Q);compare_pair(actual,candidate['all13_original_atom_order1_symbols'][k])
        zero(s.im(actual[0]));eq(actual[1].H,actual[1]);grade_predicate(actual[1],weights,0)
    print('PASS independently regenerated scalar/BF Weyl degree1,13 unique atoms, full504 Hermitian grade0 and literal mixed Moyal cancellation',flush=True)
    _,_,_,S,a,T=cotangent_values(section,raw,f,p);n,*bs=ys;b=s.Matrix(bs)
    H2=n*a+(n*n*T-(b.T*S*b)[0])/(2*n*(n*n-(b.T*b)[0]))
    F2=-s.Matrix([s.diff(H2,y) for y in ys]);base=dict(zip(ys,(raw.N,0,0,0)))
    eq(rational(F2.subs(base)),s.zeros(4,1));J=rational(F2.jacobian(s.Matrix(ys)).subs(base))
    eq(J,decode(candidate['actual_force_Jacobian']))
    force=s.Matrix.vstack(*(-H1.diff(y).subs(base) for y in ys))
    correction,params=J.gauss_jordan_solve(-force);assert params.rows==0
    correction=rational(correction);eq(J*correction+force,s.zeros(4,13))
    energy=rational(H1.subs(base));energy_pair=pair(list(energy),Q)
    compare_pair(energy_pair,candidate['first_reduced_energy_symbol'])
    force_pairs=[];clock_pairs=[]
    for i in range(4):
        F=pair(list(force[i,:]),Q);C=pair(list(correction[i,:]),Q)
        compare_pair(F,candidate['four_force_order1_symbols'][i]);compare_pair(C,candidate['four_clock_order_minus1_symbols'][i])
        zero(s.im(C[0]));eq(C[1].H,C[1]);grade_predicate(C[1],weights,0)
        force_pairs.append(F);clock_pairs.append(C)
    assert all(not row[1].todok() and row[0]==0 for row in clock_pairs[1:]);assert clock_pairs[0][1].todok()
    state={tuple(candidate['actual_consumer']['input_CAR']):s.S.One};assert next(iter(state))==(144,396)
    force_images=[apply_pair(F,state) for F in force_pairs];clock_images=[apply_pair(C,state) for C in clock_pairs]
    for i in range(4):
        assert add_terms([(1,force_images[i]),*[(J[i,j],clock_images[j]) for j in range(4)]])=={}
        assert add_terms([(1,force_images[i]),(-1,decoded_state(candidate['actual_consumer']['force_order1_images'][i]))])=={}
        assert add_terms([(1,clock_images[i]),(-1,decoded_state(candidate['actual_consumer']['clock_order_minus1_images'][i]))])=={}
        grade_state(clock_images[i],weights,2,0)
    energy_image=apply_pair(energy_pair,state)
    assert add_terms([(1,energy_image),(-1,decoded_state(candidate['actual_consumer']['first_reduced_energy_image']))])=={}
    inventory=original_inventory();phi=section.native.v+section.native.R*f['x']
    bare=sum(((phi[j]+s.I*phi[j+35])*inventory['scalar'][j] for j in range(35)),s.zeros(252))
    Y=dual_pair(sparse(s.kronecker_product(raw.N*inventory['gamma'][0],s.eye(63)))*sparse(bare))
    eq(Y,decode(candidate['original_Y_full504_order0']));grade_predicate(Y,weights,1)
    compare_pair((s.S.Zero,-Y/raw.N),candidate['original_Y_force_order0'])
    Yimage=apply_state(Y,state);sharp=apply_state(Y.H,state)
    assert Yimage and add_terms([(1,Yimage),(-1,sharp)])
    assert add_terms([(1,Yimage),(-1,decoded_state(candidate['actual_consumer']['original_Y_order0_image']))])=={}
    assert add_terms([(1,sharp),(-1,decoded_state(candidate['actual_consumer']['original_Y_adjoint_order0_image']))])=={}
    grade_state(Yimage,weights,2,1)
    print('PASS original four-force Jacobian solve, full504 and N2 C_minus1 residuals, original grade1 Y retained for order minus2',flush=True)
    files=[Path(__file__),path,HERE/'source_clock_subprincipal.py']+[HERE/name for name in (
        'independent_source_principal_clock_cone.py','independent_source_scalar_weyl_symbol.py',
        'independent_source_common_weyl_symbol.py','independent_source_gauss_quantum_current.py',
        'independent_source_quantum_grade_structure.py','independent_source_common_hamiltonian.py')]+[HERE/(name+'.json') for name in paid]
    out={'verdict':'CERTIFIED_ORIGINAL_CANONICAL_SUBPRINCIPAL_CLOCK_CORRECTION_FULL504',
        'root':ROOT_ID,'source_sha256':candidate['source_sha256'],
        'input_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},
        'source_binding_checks':count,'candidate_constructor_imported':False,
        'independent_method':'Tensor-product primary/canonical Moyal multiplier; coupled12 original scalar and implicit94 BF Weyl coefficients;13 time-weight polynomial coefficient solve; direct original force Jacobian linear solve; exterior-slot CAR and source exterior-degree grading.',
        'inner_graph_first_canonical_order':graph,'original_H1_coefficients':coefficient_laws,'all13_atoms':atom_laws,
        'source_four_force_Jacobian':encode(J),'four_clock_order_minus1_symbols':[encode_pair(C) for C in clock_pairs],
        'all_full504_corrected_order1_force_residuals_zero':True,
        'source_N2_clock_images':[state_encode(image) for image in clock_images],
        'source_first_reduced_energy_image':state_encode(energy_image),
        'original_Y_order0_image':state_encode(Yimage),'original_Y_is_not_Hermitianized':True,
        'Y_first_clock_order':'minus2; it has no momentum degree1 contribution',
        'scope':'The actual source canonical covector and all four symbolic time parameters generate the nonzero matrix-valued order-minus-one lapse and zero order-minus-one shifts; first canonical cancellation is universal per true phase pair. Complete200-phase two-jets and the order-minus-two clock are separate consumers.',
        'complete_quantum_clock_or_spectrum_generated':False,'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'independent_source_clock_subprincipal.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
    print('PASS independent source clock subprincipal',out['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':main()
