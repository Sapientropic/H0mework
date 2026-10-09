#!/usr/bin/env python3
"""Independent source and complete-row audit of the peripheral scalar Green map.

No candidate program is imported. Exterior actions use creation/annihilation
bits; the original real Euler matrix is assembled from its actual bilinear
action. Inverses are checked against independent chiral minors. Spatial Fourier
substitution is performed only after the original complex coefficients have
been realified.
"""
from __future__ import annotations

import argparse
import itertools
import json
from pathlib import Path
import re
import time

import sympy as s


def clean(matrix):
    return s.SparseMatrix(matrix).applyfunc(s.expand)


def equal(left, right):
    assert left.shape == right.shape
    assert all(s.expand(value) == 0 for value in s.SparseMatrix(left-right).todok().values())


def realify(matrix):
    """Realify constant internal-complex coefficients, before external Fourier i."""
    out = s.MutableSparseMatrix(2*matrix.rows, 2*matrix.cols, {})
    for (i,j),value in s.SparseMatrix(matrix).todok().items():
        real,imag = s.expand_complex(value).as_real_imag()
        out[i,j] = real
        out[i,j+matrix.cols] = -imag
        out[i+matrix.rows,j] = imag
        out[i+matrix.rows,j+matrix.cols] = real
    return s.SparseMatrix(out)


def exterior(matrix, degree):
    words = list(itertools.combinations(range(7),degree))
    masks = [sum(1 << i for i in word) for word in words]
    positions = {mask:i for i,mask in enumerate(masks)}
    result = s.MutableSparseMatrix(len(words),len(words),{})
    for col,mask in enumerate(masks):
        for old in range(7):
            if not mask & (1 << old):
                continue
            removed = mask ^ (1 << old)
            sign_old = (-1)**((mask & ((1 << old)-1)).bit_count())
            for new in range(7):
                if removed & (1 << new):
                    continue
                sign_new = (-1)**((removed & ((1 << new)-1)).bit_count())
                result[positions[removed | (1 << new)],col] += sign_old*sign_new*matrix[new,old]
    return s.SparseMatrix(result)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,required=True)
    args = parser.parse_args()
    started = time.monotonic()
    root = args.root.resolve()
    base = root/'Verification/physics/low-energy-phenomenology'
    core = root/'Lean/SaturationMonoid/PhysicsCore'
    directory = base/'scalar-exchange'
    receipt = json.loads((directory/'receipt.json').read_text())
    assert receipt == json.loads(Path('/tmp/scalar-exchange-audit.json').read_text())
    sector = json.loads((base/'active-sector/receipt.json').read_text())
    phase = json.loads((base/'full-phase/receipt.json').read_text())
    scalar = json.loads((base/'real-scalar-sector/receipt.json').read_text())
    vertices = json.loads((base/'matter-vertices/receipt.json').read_text())
    exchange = json.loads((base/'matter-vertices/exchange.json').read_text())
    u,*r = s.symbols('u r1 r2 r3',real=True)
    p = s.symbols('p0:4',real=True)
    variables = [u,*r]
    symbols = {str(x):x for x in variables+list(p)}

    def decode(record):
        return s.SparseMatrix(*record['shape'], {(i,j):s.sympify(value,locals=symbols)
            for i,j,value in record['entries']})

    def expression(value):
        return s.sympify(value,locals=symbols)

    n = s.sqrt(s.Rational(54,125))
    kappa = s.sqrt(2)
    alpha = 3*kappa/5
    frequency = s.simplify(3*n*(kappa-alpha)/2)
    assert n == expression(receipt['source_lapse']) == expression(phase['source_lapse'])
    assert alpha == expression(receipt['source_gauge_scale'])
    assert n > 0 and n*n == s.Rational(54,125) and alpha*alpha == s.Rational(18,25)
    scaled_p = [n*kappa*u,*[kappa*x for x in r]]
    substitution = dict(zip(p,scaled_p))
    reverse = dict(zip(variables,[-x for x in variables]))
    zero = dict.fromkeys(variables,0)

    gamma = []
    text = (core/'DiracCliffordRepresentation.lean').read_text()
    for name in ('Zero','One','Two','Three'):
        literal = re.search(r'def diracGamma'+name+r'\s*:.*?:=\s*!!\[(.*?)\]',text,re.S).group(1)
        gamma.append(s.SparseMatrix([[s.sympify(v.strip().replace('Complex.I','I'))
            for v in row.split(',')] for row in literal.split(';')]))
    color_text = (core/'Stage9C/Material/SpinPair/ColorDoublet.lean').read_text()
    color_text = color_text.split('def sourceColorPauli',1)[1].split('theorem',1)[0]
    color = [s.SparseMatrix([[s.sympify(v.strip().replace('Complex.I','I')) for v in row.split(',')]
        for row in literal.split(';')]) for literal in re.findall(r'!!\[(.*?)\]',color_text,re.S)]
    assert len(color) == 3
    names = ['colorZeroIndex','colorOneIndex','colorTwoIndex','weakZeroIndex',
        'weakOneIndex','hyperPlusIndex','hyperMinusIndex']
    text = (core/'SU7ExteriorYukawaMassSpectrum.lean').read_text()
    text = text.split('def finiteGenerationScalarSubset :',1)[1].split('\ndef ',1)[0]
    vacuum = {tuple(sorted(names.index(name.strip()) for name in term.split(','))):1
        for term in re.findall(r'\|\s*[01],\s*[01]\s*=>\s*\{([^}]+)\}',text)}
    assert len(vacuum) == 4
    bases = {d:list(itertools.combinations(range(7),d)) for d in (6,2,4)}
    internal = [(d,word) for d in (6,2,4) for word in bases[d]]
    eye70 = s.SparseMatrix(s.eye(70))
    fundamental = {}
    for group in ((0,1,2),(3,4)):
        for a,b in itertools.combinations(group,2):
            fundamental[f'A{a}{b}'] = s.SparseMatrix(7,7,{(a,b):1,(b,a):-1})
            fundamental[f'S{a}{b}'] = s.SparseMatrix(7,7,{(a,b):s.I,(b,a):s.I})
        for a in group[:-1]:
            fundamental[f'D{a}-{group[-1]}'] = s.SparseMatrix(7,7,{(a,a):s.I,(group[-1],group[-1]):-s.I})
    fundamental['Y'] = s.diag(0,0,0,0,0,s.I,-s.I)
    assert list(fundamental) == sector['p286_labels']
    v = s.Matrix([vacuum.get(word,0) for word in bases[4]])
    orbit_complex = s.Matrix.hstack(*[exterior(matrix,4)*v for matrix in fundamental.values()])
    orbit = s.SparseMatrix.vstack(orbit_complex.applyfunc(s.re),orbit_complex.applyfunc(s.im))
    equal(orbit,decode(sector['scalar_orbit']))
    independent = list(s.Matrix(orbit).rref()[1])
    assert independent == sector['scalar_orbit_independent_columns']
    J = orbit[:,independent]
    equal(J,decode(sector['J_basis']))
    gram = J.T*J
    PJ = clean(J*gram.inv()*J.T)
    P = clean(eye70-PJ)
    equal(P,decode(receipt['peripheral_projector']))
    rho = [realify(exterior(s.diag(matrix,s.zeros(5)),4)) for matrix in color]
    for j in range(3):
        equal(rho[j],s.SparseMatrix(scalar['background_color'][j]['full']).applyfunc(s.sympify))
        equal(rho[j].T,-rho[j])
        equal(P*rho[j],rho[j]*P)
        equal(exterior(s.diag(color[j],s.zeros(5)),4)*v,s.zeros(35,1))
    casimir = clean(sum((matrix*matrix for matrix in rho),s.zeros(70)))
    Pd = clean(-4*casimir*P/3)
    Ps = clean(P-Pd)
    equal(Ps,decode(receipt['singlet_projector']))
    equal(Pd,decode(receipt['doublet_projector']))
    for projection,dimension in ((PJ,9),(P,61),(Ps,25),(Pd,36)):
        equal(projection.T,projection)
        equal(projection*projection,projection)
        assert s.trace(projection) == dimension
    equal(Ps*Pd,s.zeros(70))
    for i,j in itertools.product(range(3),repeat=2):
        equal(rho[i]*rho[j]*Pd+rho[j]*rho[i]*Pd,-s.Rational(int(i==j),2)*Pd)
        equal(rho[i]*Ps,s.zeros(70))
    # These three actual endomorphisms give nine real quaternion modules.
    for i,j,k in ((0,1,2),(1,2,0),(2,0,1)):
        equal((2*rho[i]*Pd)*(2*rho[j]*Pd),-2*rho[k]*Pd)
    covariant = [kappa*r[i]*eye70+alpha*rho[i] for i in range(3)]
    operator = clean((scaled_p[0]**2/n**2-2)*eye70-
        sum((matrix*matrix for matrix in covariant),s.zeros(70)))
    equal(operator,decode(receipt['normalized_full_scalar_operator']))
    equal(operator.subs(reverse,simultaneous=True).T,operator)
    a = 2*u*u-2*sum(x*x for x in r)-2
    b = a+s.Rational(27,50)
    R = clean(sum((r[i]*rho[i] for i in range(3)),s.zeros(70))*P)
    d = s.expand(b*b+2*alpha*alpha*sum(x*x for x in r))
    numerator = decode(receipt['peripheral_scalar_green_numerator'])
    denominator = expression(receipt['peripheral_scalar_green_denominator'])
    equal(numerator,clean(d*Ps+a*(b*Pd+2*kappa*alpha*R)))
    assert s.expand(denominator-n*a*d) == 0
    equal(n*operator*numerator,denominator*P)
    equal(numerator*n*operator,denominator*P)
    equal(P*numerator,numerator)
    equal(numerator*P,numerator)
    equal(numerator.subs(reverse,simultaneous=True).T,numerator)
    # The source equation in ScalarBlock.Euler is -N*covariantKleinGordon.
    # Its inverseFactor is (-N^-2,1,1,1), fixing both time sign and N here.
    scalar_euler = (core/'LowEnergy/ScalarBlock/Euler.lean').read_text()
    assert '-lapse*parameter*scalarCoordinatePairingRe test (covariantKleinGordon profile point)' in scalar_euler
    assert '![-(lapse^2)⁻¹,1,1,1]' in (core/'LowEnergy/ScalarBlock/Fields.lean').read_text()
    lam,*k = s.symbols('lam k1 k2 k3',real=True)
    fourier = {u:lam/(n*kappa),**{r[i]:s.I*k[i]/kappa for i in range(3)}}
    physical_a = lam**2/n**2+sum(x*x for x in k)-2
    physical_b = physical_a+s.Rational(27,50)
    physical_R = sum((k[i]*rho[i] for i in range(3)),s.zeros(70))*P
    assert s.expand(a.subs(fourier)-physical_a) == 0
    assert s.expand(d.subs(fourier)-physical_b**2+alpha**2*sum(x*x for x in k)) == 0
    equal((2*kappa*alpha*R).subs(fourier),2*s.I*alpha*physical_R)
    print('PASS actual J rank9, P rank61, Casimir 25+36 and quaternion identities; original N/time sign and full-four-momentum two-sided scalar inverse',flush=True)

    def yukawa(coefficients):
        small = s.MutableSparseMatrix(7,21,{})
        for col,two in enumerate(bases[2]):
            for four,value in coefficients.items():
                if set(two).isdisjoint(four):
                    small[bases[6].index(tuple(sorted(two+four))),col] += value*(-1)**sum(a>b for a in two for b in four)
        inside = s.MutableSparseMatrix(63,63,{})
        inside[:7,7:28] = small
        return clean(s.kronecker_product(s.diag(0,0,1,1),inside))

    eye63 = s.SparseMatrix(s.eye(63))
    Gamma = [clean(s.kronecker_product(g,eye63)) for g in gamma]
    S = clean(s.kronecker_product(gamma[0]*s.diag(-1,-1,1,1),eye63))
    Q = clean(s.kronecker_product(s.diag(-1,-1,1,1),eye63)+
        2*s.kronecker_product(s.eye(4),s.diag(*[int(degree==6) for degree,_ in internal])))
    equal(Q,decode(phase['phase_generator']))
    C = [s.I*Gamma[mu]/(n if mu==0 else 1) for mu in range(4)]
    rotations = [gamma[2]*gamma[3],gamma[3]*gamma[1],gamma[1]*gamma[2]]
    connections = [clean(kappa/2*s.kronecker_product(rotations[j],eye63)+
        alpha*s.kronecker_product(s.eye(4),s.diag(*[
            exterior(s.diag(color[j],s.zeros(5)),degree) for degree in (6,2,4)]))) for j in range(3)]
    B = clean(sum((C[j+1]*connections[j] for j in range(3)),s.zeros(252)))
    Y = yukawa(vacuum)
    constant = clean(B+Y+frequency/n*Gamma[0]*Q)
    equal(Y,decode(phase['original_Y']))
    equal(B,decode(phase['original_constant_B']))
    equal(constant,decode(phase['stationary_primal_constant']))
    for mu in range(4):
        equal(C[mu],decode(phase['principal_coefficients'][mu]))
    seed = s.MutableSparseMatrix(252,1,{})
    for spin,word,value in ((0,(1,5),1),(1,(0,5),-1),(2,(1,5),1),(3,(0,5),-1)):
        seed[spin*63+internal.index((2,word)),0] = value
    chi = clean(kappa*seed.T*S)
    equal(constant*seed,s.zeros(252,1))
    equal(chi*constant,s.zeros(1,252))
    scalar_vertices = [yukawa({word:1}) for word in bases[4]]
    M = clean(s.Matrix.hstack(*[vertex*seed for vertex in scalar_vertices]))
    equal(M,decode(phase['stationary_scalar_mixing']))
    for vertex in scalar_vertices:
        equal(chi*vertex,s.zeros(1,252))
    D = clean(constant+sum((scaled_p[mu]*C[mu] for mu in range(4)),s.zeros(252)))
    # Coefficient-wise realification is distinct from realifying Fourier-valued D.
    DR = clean(realify(constant)+sum((scaled_p[mu]*realify(C[mu]) for mu in range(4)),s.zeros(504)))
    equal(DR,realify(D))
    MR = realify(M)
    dual_pairing = s.diag(s.eye(252),-s.eye(252),cls=s.SparseMatrix)
    Msharp = clean(MR.T*dual_pairing)
    six = [spin*63+i for spin in range(4) for i in range(7)]
    other = [i for i in range(252) if i not in six]
    real_six = six+[252+i for i in six]
    real_other = other+[252+i for i in other]
    equal(M[other,:],s.zeros(224,35))
    equal(D.extract(other,six),s.zeros(224,28))
    equal(Y[:,six],s.zeros(252,28))
    equal(MR*PJ,s.zeros(504,70))
    equal(PJ*Msharp,s.zeros(70,504))
    equal(MR.extract(real_six,range(70)),decode(receipt['source_phase_mixing_real']))
    assert M.rank() == 9 and MR.rank() == 18
    # The full scalar/primal/independent-dual Hessian of the original real action.
    # Its row order is scalar70, primal504, dual504; no dual Hermitian replacement.
    H = s.MutableSparseMatrix(1078,1078,{})
    H[:70,:70] = n*operator
    H[:70,574:] = n*Msharp
    H[574:,:70] = n*dual_pairing*MR
    H[574:,70:574] = n*dual_pairing*DR
    H[70:574,574:] = n*DR.subs(reverse,simultaneous=True).T*dual_pairing
    H = clean(H)
    equal(H.subs(reverse,simultaneous=True).T,H)
    assert H[70:574,:70] == s.zeros(504,70)
    assert H[:70,70:574] == s.zeros(70,504)
    print('PASS actual full252 C/B/Y/Q and nonzero M rank18; original 1078 real Euler matrix with independent-dual signs and signed momentum',flush=True)

    blocks = receipt['original_primal_readback_blocks']
    actual_D6 = clean(D.extract(six,six)/kappa)
    # Obtain components independently with union-find, rather than candidate DFS.
    parents = list(range(28))
    def find(i):
        while parents[i] != i:
            i = parents[i]
        return i
    for i,j in actual_D6.todok():
        parents[find(i)] = find(j)
    groups = {}
    for i in range(28):
        groups.setdefault(find(i),[]).append(i)
    support = sorted(groups.values())
    assert support == [block['complex_degree_six_indices'] for block in blocks]
    assert sorted(map(len,support)) == [4,4,4,4,4,8]
    all_real_ids = []
    numerator_response_rows = []
    denominators_at_origin = []
    independent_minor_degrees = []
    nonzero_primal_entries = 0
    for block in blocks:
        ids = block['complex_degree_six_indices']
        real_ids = ids+[28+i for i in ids]
        assert real_ids == block['real_degree_six_indices']
        all_real_ids += real_ids
        Db = actual_D6.extract(ids,ids)
        equal(Db,decode(block['normalized_complex_operator']))
        adj = decode(block['complex_inverse_numerator'])
        det = expression(block['complex_inverse_denominator'])
        equal(Db*adj,det*s.eye(len(ids)))
        equal(adj*Db,det*s.eye(len(ids)))
        h = len(ids)//2
        equal(Db[:h,:h],s.zeros(h))
        equal(Db[h:,h:],s.zeros(h))
        # Small classical minors give a second inverse derivation.
        A,Bc = Db[:h,h:],Db[h:,:h]
        da,db = s.expand(A.det(method='berkowitz')),s.expand(Bc.det(method='berkowitz'))
        assert da != 0 and db != 0
        adjA,adjB = clean(A.adjugate(method='berkowitz')),clean(Bc.adjugate(method='berkowitz'))
        equal(adj[:h,h:]*db,det*adjB)
        equal(adj[h:,:h]*da,det*adjA)
        equal(adj[:h,:h],s.zeros(h))
        equal(adj[h:,h:],s.zeros(h))
        independent_minor_degrees.append([s.Poly(x,*variables).total_degree() for x in (da,db)])
        real_den = s.expand(det*s.conjugate(det))
        real_num = realify(clean(adj*s.conjugate(det)))
        real_Db = DR.extract([six[i] for i in ids]+[252+six[i] for i in ids],
            [six[i] for i in ids]+[252+six[i] for i in ids])/kappa
        equal(real_Db*real_num,real_den*s.eye(2*len(ids)))
        equal(real_num*real_Db,real_den*s.eye(2*len(ids)))
        fn = decode(block['primal_green_numerator'])
        fd = expression(block['primal_green_denominator'])
        assert s.expand(fd-kappa*real_den*denominator) == 0
        actual_ids = [six[i] for i in ids]+[252+six[i] for i in ids]
        Mb = MR.extract(actual_ids,range(70))
        equal(fn,-real_num*Mb*numerator)
        equal(kappa*real_Db*fn+kappa*real_den*Mb*numerator,s.zeros(2*len(ids),70))
        # Check the actual full Euler rows, including the N*complex-dual pairing.
        primal_rows = [70+i for i in actual_ids]
        dual_rows = [574+i for i in actual_ids]
        equal(H.extract(dual_rows,primal_rows)*fn+
            H.extract(dual_rows,range(70))*numerator*kappa*real_den,s.zeros(len(dual_rows),70))
        other_equation_rows = [i for i in range(1078) if i not in dual_rows]
        equal(H.extract(other_equation_rows,primal_rows)*fn,s.zeros(len(other_equation_rows),70))
        nonzero_primal_entries += len(fn.todok())
        denominators_at_origin.append(str(real_den.subs(zero)))
        numerator_response_rows += actual_ids
        print(f'PASS source chiral inverse and all1078 Euler-row incidence for complex block {len(ids)}',flush=True)
    assert sorted(all_real_ids) == list(range(56))
    assert sorted(numerator_response_rows) == sorted(real_six)
    assert nonzero_primal_entries > 0
    # Every remaining original matter row is exactly zero, not discarded.
    untouched = list(range(70,574))+[574+i for i in real_other]
    equal(H.extract(untouched,range(70)),s.zeros(len(untouched),70))
    equal(H.extract(range(70),range(70))*numerator,denominator*P)
    equal(MR*numerator*PJ,s.zeros(504,70))
    assert clean(MR*numerator) != s.zeros(504,70)
    wrong_pairing = MR.T*MR
    assert wrong_pairing != Msharp*MR

    # Actual source isolation: scalar current legs vanish by the real J projection;
    # the induced primal lives in Lambda6, outside every occupied active H leg.
    for mu in range(4):
        cov = scaled_p[mu]*eye70+(alpha*rho[mu-1] if mu else s.zeros(70))
        equal(orbit.T*cov*P,s.zeros(12,70))
    raw_scalar = []
    boson_zero_count = 0
    for item in vertices['primitive_vertices']:
        V = decode(item['operator'])
        if item['group'] == 'scalar':
            part,col = item['coordinate']
            equal(V,n*s.I**part*scalar_vertices[col])
            assert part*35+col == len(raw_scalar)
            raw_scalar.append(V)
        else:
            # These already-certified vertices retain full original coframe/phase jets.
            equal((chi*V).extract([0],six),s.zeros(1,28))
            boson_zero_count += 1
    assert boson_zero_count == 88 and len(raw_scalar) == 70
    active_ops = {item['field']:decode(item['operator'])
        for item in vertices['active_289_bosonic_source_operators']}
    for col in range(9):
        equal(sum((J[row,col]*raw_scalar[row] for row in range(70) if J[row,col]),s.zeros(252)),active_ops[col])
    equal(decode(receipt['full_scalar_source_split_active_map']),J.T)
    equal(decode(receipt['full_scalar_source_split_peripheral_map']),P)
    equal(J*gram.inv()*J.T+P,eye70)
    equal(J.T*P,s.zeros(9,70))
    # The same 97-dimensional active source normal form is consumed, with its
    # nine compatibility rows retained for general external bilinear sources.
    source_fields = exchange['source_fields']
    assert source_fields[:9] == [{'group':'scalar_J','coordinate':[i]} for i in range(9)]
    assert exchange['source_field_indices'][:9] == list(range(9))
    source_split = s.diag(J.T,s.eye(88),cls=s.SparseMatrix)
    assert source_split.shape == (97,158)
    compatibility = clean(decode(exchange['local_source_compatibility_map'])*source_split)
    assert compatibility.shape == (9,158) and compatibility != s.zeros(9,158)
    source_P = s.SparseMatrix.hstack(P,s.zeros(70,88))
    source_lift = s.SparseMatrix.hstack(J*gram.inv(),s.zeros(70,88))
    equal(source_lift*source_split+source_P,s.SparseMatrix.hstack(eye70,s.zeros(70,88)))
    # No source substitution can remove an inherited nonzero compatibility map.
    # The returned classical exchange retains A79/B24 inverses on their domain.
    assert 'compatibility(p)*j(p)=0' in exchange['domain']
    print('PASS all70 source vertices, actual9 active source normalization,88 remaining occupied current legs and inherited nonzero9 source compatibility rows',flush=True)

    static = clean(numerator.subs(zero)/denominator.subs(zero))
    equal(static,decode(receipt['scalar_static_green']))
    equal(-static/2,Ps/(4*n)+25*Pd/(73*n))
    assert denominator.subs(zero) != 0
    # Explicit negative controls at the actual source matrices.
    assert clean(operator*numerator-denominator*P) != s.zeros(70)  # omit N
    assert clean(n*operator*(-numerator)-denominator*P) != s.zeros(70)
    assert clean(MR*numerator) != s.zeros(504,70)  # erase primal feedback
    assert clean((MR*Ps).row_join(MR*Pd)).rank() == 18
    witness = next(((i,j) for (i,j),value in realify(C[1]).todok().items() if value),None)
    assert witness is not None
    right_fourier = s.I*realify(C[1])
    wrong_fourier = realify(s.I*C[1])
    assert right_fourier != wrong_fourier
    assert gram != s.eye(9)
    assert J.T != gram.inv()*J.T
    assert any(value == '0' for value in denominators_at_origin)
    print('PASS exact static contact and negative controls: lapse,source sign,missing M,complex/Fourier order,active-source Gram normalization',flush=True)

    output = {
        'status':'PASS','receipt_replay_identical':True,
        'source':'original scalar Euler, Clifford/Pauli/exterior matrices and independent-dual real action',
        'projector_ranks':{'J':9,'peripheral':61,'singlet':25,'quaternion_real':36},
        'quaternion_blocks':9,'all_four_formal_momenta':True,
        'source_lapse':str(n),'source_gauge_scale':str(alpha),
        'physical_scalar_green':'1/N [Ps/a+(b Pd+2 i alpha rho(k) P)/(b^2-alpha^2 |k|^2)]',
        'a':'lambda^2/N^2+|k|^2-2','b':'a+27/50',
        'original_complex_mixing_rank':9,'original_real_mixing_rank':18,
        'scalar_primal_independent_dual_Euler_matrix_shape':[1078,1078],
        'all_original_scalar_rows':70,'all_original_primal_real_rows':504,
        'all_original_independent_dual_real_rows':504,
        'remaining_complex_matter_coordinates_checked':224,
        'degree_six_complex_blocks':list(map(len,support)),
        'independent_chiral_minor_degrees':independent_minor_degrees,
        'real_block_denominators_at_origin':denominators_at_origin,
        'primal_green_nonzero_numerator_entries':nonzero_primal_entries,
        'positive_source_induced_fields':'eta=-G z, zeta=0, xi=+D6^-1 M G z',
        'all_original_bosonic_current_legs_zero':boson_zero_count,
        'all_scalar_vertices_from_source':70,'actual_active_scalar_vertices':9,
        'full_source_split_shape':[97,158],
        'inherited_compatibility_shape':[9,158],
        'inherited_compatibility_map_nonzero':True,
        'static_exchange':'z^T Ps z/(4 N)+25 z^T Pd z/(73 N)',
        'negative_controls':['omit_volume_N','reverse_source_response_sign',
            'erase_nonzero_primal_feedback','realify_after_external_Fourier_i',
            'replace_covector_J_transpose_by_coordinate_left_inverse',
            'replace_independent_dual_by_Hermitian_pairing'],
        'full_field_inverse_regular_at_origin_claimed':False,
        'canonical_nonlinear_preparation_preservation_claimed':False,
        'new_Lean_end_to_end_matrix_theorem_claimed':False,
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (directory/'audit/independent-receipt.json').write_text(json.dumps(output,indent=2)+'\n')
    print(f'PASS complete independent source audit ({output["elapsed_seconds"]} s)',flush=True)


if __name__ == '__main__':
    main()
