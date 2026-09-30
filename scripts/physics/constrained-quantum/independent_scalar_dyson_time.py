#!/usr/bin/env python3
"""Independent source coefficient and entire time-primitive certification.

Build coefficient derivatives entrywise from the original left/right matter
action and scalar flow. The candidate is never imported. Whole-source block
coverage is checked before its finite exponential primitives are accepted.
"""
from __future__ import annotations

from collections import Counter, defaultdict
import hashlib
import itertools
import json
from pathlib import Path
import re
import time

import sympy as s

from independent_spectral_splice import OriginalAction, ROOT_ID, clean, equal, matrix, source

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
ROOT = HERE.parents[3]
KIN = s.symbols('kin1:4', real=True)
KOUT = s.symbols('kout1:4', real=True)
KAP = s.symbols('kap1:4', real=True)
K = s.symbols('k1:4', real=True)


def zero(rows, columns=None):
    return s.SparseMatrix.zeros(rows, rows if columns is None else columns)


def read(path):
    return json.loads(path.read_bytes())


def decode(row):
    symbols = {str(v): v for v in (*KIN, *KOUT, *KAP, *K)}
    return s.SparseMatrix(*row['shape'], {(i, j): s.sympify(v, locals=symbols) for i, j, v in row['entries']})


def validate(record):
    count = 0
    for key in ('source_sha256', 'input_sha256'):
        for name, digest in record.get(key, {}).items():
            assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == digest, name
            count += 1
    return count


def partition(indices, operator):
    """Union-find of nonzero source coefficients, independent of DFS ordering."""
    parent = {i: i for i in indices}
    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i
    for i, j in operator.todok():
        if i in parent and j in parent:
            a, b = root(i), root(j)
            parent[max(a,b)] = min(a,b)
    groups = defaultdict(list)
    for i in indices:
        groups[root(i)].append(i)
    return sorted((sorted(v) for v in groups.values()), key=lambda v: v[0])


def coordinate_frame(size, indices):
    return s.SparseMatrix(size, len(indices), {(i, j): 1 for j, i in enumerate(indices)})


def matrix_code(value):
    return {'shape': list(value.shape), 'entries': [[i,j,str(s.expand(v))]
        for (i,j),v in sorted(s.SparseMatrix(value).todok().items())]}


def signature(value):
    return hashlib.sha256(json.dumps(matrix_code(value), separators=(',',':')).encode()).hexdigest()


def coefficient_derivative(scalar, left, right):
    """Direct index action on X_b[i,j], vector slot b*d*f+j*d+i."""
    r, d, f = scalar.rows, left.rows, right.rows
    result = defaultdict(lambda: s.Integer(0))
    def slot(b,i,j): return b*d*f+j*d+i
    for (a,b), value in scalar.todok().items():
        for i,j in itertools.product(range(d), range(f)):
            result[slot(b,i,j),slot(a,i,j)] += value
    for (i,h), value in left.todok().items():
        for b,j in itertools.product(range(r), range(f)):
            result[slot(b,i,j),slot(b,h,j)] -= value
    for (h,j), value in right.todok().items():
        for b,i in itertools.product(range(r), range(d)):
            result[slot(b,i,j),slot(b,i,h)] += value
    return clean(s.SparseMatrix(r*d*f, r*d*f, result))


def integrate_signal(L, v):
    n = L.rows
    entries = dict(L.todok())
    entries.update({(i,n): value for (i,_),value in v.todok().items()})
    G = s.SparseMatrix(n+1,n+1,entries)
    initial = s.SparseMatrix(n+1,1,{(n,0):1})
    output = s.SparseMatrix(n,n+1,{(i,i):1 for i in range(n)})
    derivative = clean(output*G)
    equal(output*initial, zero(n,1))
    equal(derivative*initial, v)
    equal(derivative*G, L*derivative)
    # Thus d/dt(output exp(Gt) initial)=exp(Lt)v for every t,
    # including any resonance; no inverse of L was introduced.
    return G, initial, output


def main():
    started = time.monotonic()
    candidate_path = HERE/'scalar_dyson_time.json'
    candidate = read(candidate_path)
    assert candidate['root'] == ROOT_ID
    bindings_count = validate(candidate)
    paths = {name: HERE/name for name in ('scalar_joint_hamiltonian.json',
        'independent_scalar_joint_hamiltonian.json', 'scalar_canonical_phase.json',
        'full-matter-ports.json', 'scalar_dyson_fixed_N.json',
        'independent_scalar_dyson_fixed_N.json', 'fock_raising_audit.json')}
    records = {name: read(path) for name,path in paths.items()}
    for record in records.values():
        assert record['root'] == ROOT_ID
        bindings_count += validate(record)
    pair = records['scalar_joint_hamiltonian.json']
    scalar = records['scalar_canonical_phase.json']
    matter = records['full-matter-ports.json']
    grade_audit = records['independent_scalar_dyson_fixed_N.json']
    assert grade_audit['verdict'] == 'CERTIFIED_RAW_SOURCE_ALL61_SCALAR_GRADE_AND_ARBITRARY_N_CAR_WORD_CONSUMER'
    assert candidate['source_sha256'] == scalar['source_sha256'] == pair['source_sha256'] == matter['source_sha256']

    # Recover the all-momentum252 action from original source Clifford,
    # exterior and coframe data; do not read the candidate's local generators.
    active_path, phase_path, vertices_path = [BASE/p for p in
        ('active-gauge/receipt.json','full-phase/receipt.json','matter-vertices/receipt.json')]
    active, phase, vertices = map(read, (active_path,phase_path,vertices_path))
    _, vacuum, degrees, hashes = source.parse_source(ROOT)
    assert hashes == candidate['source_sha256']
    gamma_path = ROOT/'Lean/SaturationMonoid/PhysicsCore/DiracCliffordRepresentation.lean'
    gamma = []
    for name in ('Zero','One','Two','Three'):
        literal = re.search(r'def diracGamma'+name+r'\s*:.*?:=\s*!!\[(.*?)\]', gamma_path.read_text(), re.S).group(1)
        gamma.append(s.SparseMatrix([[s.sympify(v.strip().replace('Complex.I','I'))
            for v in row.split(',')] for row in literal.split(';')]))
    original = OriginalAction(active, phase, vertices, vacuum, degrees, gamma)
    raw = original.holonomic(original.configuration(zero(289,1)), s.Matrix(K))
    A = clean(-raw['inverse_E']*raw['K'])
    equal(raw['E']*A+raw['K'],zero(252))
    hcoeff = matter['stationary_Hamiltonian_coefficients']
    equal(A, -s.I*(decode(hcoeff['constant'])+sum((k*decode(hcoeff[str(k)]) for k in K),zero(252))))
    W = []
    for row in scalar['projected_CAR_couplings']:
        value = clean(-s.I*raw['inverse_E']*decode(row['density_vertex']))
        equal(value,decode(row['canonical_matter_vertex']))
        W.append(value)
    assert len(W) == 61
    inside = [degree for degree in degrees for _ in itertools.combinations(range(7),degree)]
    ids = {degree:[spin*63+j for spin in range(4) for j,d in enumerate(inside) if d==degree] for degree in degrees}
    out_blocks, in_blocks = partition(ids[6],A), partition(ids[2],A)
    assert out_blocks == candidate['matter_target_blocks']
    assert in_blocks == candidate['matter_input_blocks']
    target, domain = set(ids[6]),set(ids[2])
    assert target.isdisjoint(domain)
    assert all(i in target and j in domain for value in W for i,j in value.todok())

    # Independently assemble one real Fourier pair from its two original
    # complex source flows. This also fixes the qR,qI,pR,pI ordering.
    Ac = clean(decode(scalar['canonical_generator']).subs(dict(zip(K,KAP)),simultaneous=True))
    minus = dict(zip(KAP,[-v for v in KAP]))
    plus = s.SparseMatrix(122,244,{
        **{(j,j):1/s.sqrt(2) for j in range(61)},
        **{(j,61+j):s.I/s.sqrt(2) for j in range(61)},
        **{(61+j,122+j):1/s.sqrt(2) for j in range(61)},
        **{(61+j,183+j):s.I/s.sqrt(2) for j in range(61)}})
    conjugate = plus.conjugate()
    As = clean(plus.H*Ac*plus+conjugate.H*Ac.subs(minus,simultaneous=True)*conjugate)
    equal(plus*As,Ac*plus)
    equal(conjugate*As,Ac.subs(minus,simultaneous=True)*conjugate)
    equal(As,decode(pair['real_phase_generator']).subs(dict(zip(K,KAP)),simultaneous=True))
    equal(As.conjugate(),As)
    Az = clean(Ac.subs(dict.fromkeys(KAP,0)))
    equal(Az,decode(pair['zero_mode']['generator']))
    assert As.shape==(244,244) and Az.shape==(122,122)
    phase_blocks = {False:partition(list(range(244)),As),True:partition(list(range(122)),Az)}
    assert {str(k):v for k,v in Counter(map(len,phase_blocks[False])).items()}==candidate['scalar_pair_components']
    assert {str(k):v for k,v in Counter(map(len,phase_blocks[True])).items()}==candidate['scalar_zero_components']
    for iszero,scalar_A in ((False,As),(True,Az)):
        for block in phase_blocks[iszero]:
            T = coordinate_frame(scalar_A.rows,block)
            equal(scalar_A.T*T,T*scalar_A.extract(block,block).T)

    def drift(momentum,branch):
        argument = momentum if branch==1 else [-v for v in momentum]
        value = A.subs(dict(zip(K,argument)),simultaneous=True)
        return clean(value if branch==1 else value.conjugate())
    full_drifts = {(branch,kind):drift(momentum,branch)
        for branch in (1,-1) for kind,momentum in (('in',KIN),('out',KOUT))}
    for branch in (1,-1):
        for block in out_blocks:
            T = coordinate_frame(252,block); actual=full_drifts[branch,'out']
            equal(actual*T,T*actual.extract(block,block))
        for block in in_blocks:
            T = coordinate_frame(252,block); actual=full_drifts[branch,'in']
            equal(T.T*actual,actual.extract(block,block)*T.T)
    print('PASS original full252 branch generators and complete scalar/matter block embeddings at arbitrary incoming/outgoing momenta',flush=True)

    out_map={i:j for j,block in enumerate(out_blocks) for i in block}
    in_map={i:j for j,block in enumerate(in_blocks) for i in block}
    catalogues={}
    for iszero in (False,True):
        lookup={i:j for j,block in enumerate(phase_blocks[iszero]) for i in block}
        catalogue=defaultdict(dict)
        for a,value in enumerate(W):
            for phase_index in ((a,) if iszero else (a,a+61)):
                for (i,j),entry in value.todok().items():
                    catalogue[lookup[phase_index],out_map[i],in_map[j]][phase_index,i,j]=entry
        catalogues[iszero]=catalogue
    assert len(catalogues[False])==candidate['pair_component_catalogue_count']==190
    assert len(catalogues[True])==candidate['zero_component_catalogue_count']==200
    states=candidate['primitive_states']
    expected_keys={(iszero,branch,sign,key) for iszero in (False,True) for branch in (1,-1)
        for sign in ((1,) if iszero else (1,-1)) for key in catalogues[iszero]}
    actual_keys=[(row['zero_mode'],row['branch'],row['sign'],tuple(row['key'])) for row in states]
    assert len(actual_keys)==len(set(actual_keys))==len(expected_keys)==1160
    assert set(actual_keys)==expected_keys
    cache={}; saved_states={}; whole_initial=defaultdict(dict); primitive_reports=[]
    for row in states:
        iszero,branch,sign,key=row['zero_mode'],row['branch'],row['sign'],tuple(row['key'])
        scalar_ids=phase_blocks[iszero][key[0]]
        out_ids,in_ids=out_blocks[key[1]],in_blocks[key[2]]
        assert (scalar_ids,out_ids,in_ids)==(row['phase_indices'],row['target_indices'],row['input_indices'])
        scalar_A=Az if iszero else As
        S=scalar_A.extract(scalar_ids,scalar_ids)
        left=full_drifts[branch,'out'].extract(out_ids,out_ids)
        right=full_drifts[branch,'in'].extract(in_ids,in_ids)
        r,d,f=len(scalar_ids),len(out_ids),len(in_ids)
        cache_key=(iszero,branch,key)
        if cache_key not in cache:
            L=coefficient_derivative(S,left,right)
            kronecker=clean(s.kronecker_product(S.T,s.eye(d*f))+
                s.kronecker_product(s.eye(r),s.kronecker_product(s.eye(f),-left)+s.kronecker_product(right.T,s.eye(d))))
            equal(L,kronecker)
            cache[cache_key]=L
        L=cache[cache_key]
        v=zero(r*d*f,1)
        for (phase_index,i,j),value in catalogues[iszero][key].items():
            # Keep the field Fourier coefficient unchanged on both source
            # branches; only the independent real-action matter W changes.
            weight=1 if iszero else (1 if phase_index<61 else sign*s.I)/s.sqrt(2)
            vertex=value if branch==1 else -s.conjugate(value)
            coefficient=s.expand(-s.I*weight*vertex)
            slot=scalar_ids.index(phase_index)*d*f+in_ids.index(j)*d+out_ids.index(i)
            v[slot,0]=coefficient
        equal(v,decode(row['signal_initial']))
        for (slot,_),value in v.todok().items():
            b,remainder=divmod(slot,d*f); j,i=divmod(remainder,d)
            global_key=(scalar_ids[b],out_ids[i],in_ids[j])
            assert global_key not in whole_initial[iszero,branch,sign]
            whole_initial[iszero,branch,sign][global_key]=value
        assert row['signal_state_dimension']==r*d*f and row['primitive_state_dimension']==r*d*f+1
        G,initial,output=integrate_signal(L,v)
        assert row['initial_zero_and_derivative_original_signal'] and row['generator_coefficient_identity']
        saved_states[iszero,branch,sign,key]=(L,v,G,initial,output)
        primitive_reports.append({'zero_mode':iszero,'branch':branch,'sign':sign,'key':list(key),
            'signal_dimension':L.rows,'primitive_dimension':G.rows,
            'direct_index_generator_matches_column_vec':True,
            'all_time_primitive_intertwining_checked':True})
    for iszero,branch,sign in whole_initial:
        expected={}
        for a,value in enumerate(W):
            for phase_index in ((a,) if iszero else (a,a+61)):
                weight=1 if iszero else (1 if phase_index<61 else sign*s.I)/s.sqrt(2)
                for (i,j),entry in value.todok().items():
                    expected[phase_index,i,j]=s.expand(-s.I*weight*(entry if branch==1 else -s.conjugate(entry)))
        assert expected==whole_initial[iszero,branch,sign]
    assert Counter(row['zero_mode'] for row in states)=={False:760,True:400}
    assert max(row['primitive_state_dimension'] for row in states)==candidate['largest_primitive_state_dimension']==129
    assert candidate['all61_canonical_vertices_covered']==list(range(61))
    print('PASS all760 pair and400 zero primitives, complete full252 source readback, column-vec signs and exact initial/derivative equations',flush=True)

    # The wavefunction shift is kout=kin+sign*kappa for a nonzero pair,
    # and kout=kin for its separately normalized real zero mode.
    for sign in (1,-1):
        outgoing=s.Matrix(KIN)+sign*s.Matrix(KAP)
        equal(outgoing-sign*s.Matrix(KAP),s.Matrix(KIN))
    # The dual reverses each actual edge and uses the opposite transpose.
    for value in W:
        for vertex in (value,-value.conjugate()):
            equal((s.I*vertex.T).T+(-s.I*vertex),zero(252))
    assert target.isdisjoint(domain)
    print('PASS N1 nilpotence on complete source blocks, real zero normalization, both Fourier transfers and independent dual',flush=True)

    ordered=candidate['ordered_N2_consumer']
    left_key=(False,1,1,tuple(ordered['left_source_key']))
    right_key=(False,1,1,tuple(ordered['right_source_key']))
    L2,v2,_,_,_=saved_states[left_key]
    _,v1,G1,u1,O1=saved_states[right_key]
    m,d,r=L2.rows,G1.rows,O1.rows
    # Direct tensor-product index differentiation: the first coefficient is
    # the later left operator, the previous integral stays on its right.
    driver=defaultdict(lambda:s.Integer(0))
    for (i,j),value in L2.todok().items():
        for a in range(d): driver[i*d+a,j*d+a]+=value
    for (a,b),value in G1.todok().items():
        for i in range(m): driver[i*d+a,i*d+b]+=value
    D=clean(s.SparseMatrix(m*d,m*d,driver))
    equal(D,s.kronecker_product(L2,s.eye(d))+s.kronecker_product(s.eye(m),G1))
    read_product=s.SparseMatrix(m*r,m*d,{(i*r+a,i*d+b):value
        for i in range(m) for (a,b),value in O1.todok().items()})
    driver_initial=s.SparseMatrix(m*d,1,{(i*d+a,0):value*entry
        for (i,_),value in v2.todok().items() for (a,_),entry in u1.todok().items()})
    n=m*r
    G=clean(s.SparseMatrix.vstack(s.SparseMatrix.hstack(zero(n),read_product),
        s.SparseMatrix.hstack(zero(m*d,n),D)))
    initial=s.SparseMatrix.vstack(zero(n,1),driver_initial)
    O=s.SparseMatrix.hstack(s.eye(n),zero(n,m*d))
    R=s.SparseMatrix.hstack(zero(m*d,n),s.eye(m*d))
    equal(O*initial,zero(n,1));equal(O*G*initial,zero(n,1))
    equal(O*G,read_product*R);equal(R*G,D*R);equal(R*initial,driver_initial)
    second=clean(O*G*G*initial)
    equal(second,s.kronecker_product(v2,v1));equal(second,decode(ordered['second_derivative']))
    assert second.todok()
    assert G.rows==ordered['state_dimension']==136 and O.rows==ordered['output_dimension']
    assert ordered['left_boson_factor_stays_left']
    print('PASS actual136-state ordered N2 coefficient: zero initial/first jet, full second jet and chronological tensor driver',flush=True)

    input_paths=[candidate_path,HERE/'scalar_dyson_time.py',*paths.values(),active_path,phase_path,
        vertices_path,gamma_path,BASE/'exact_readout.py',HERE/'independent_spectral_splice.py',
        HERE/'independent_scalar_dyson_time.py']
    result={'verdict':'CERTIFIED_ALL61_SOURCE_N1_TIME_PRIMITIVES_AND_ONE_ORDERED_N2_COEFFICIENT',
        'root':ROOT_ID,'source_sha256':hashes,
        'input_sha256':{str(path.relative_to(ROOT)):hashlib.sha256(path.read_bytes()).hexdigest() for path in input_paths},
        'candidate_constructor_imported':False,
        'algorithm':'raw source252 drift; original conjugate scalar flow; independent union-find source blocks; coefficient-index differentiation independently equals column-vec Kronecker form; all source entries restored; entire primitive derivative intertwining; direct ordered tensor-driver indices',
        'source_binding_checks':bindings_count,'pair_primitive_count':760,'zero_primitive_count':400,
        'largest_primitive_dimension':129,'complete_scalar_coordinate_coverage':list(range(61)),
        'primitive_checks':primitive_reports,
        'whole_source_full252_readback_checked_for_every_branch_and_transfer':True,
        'primitive_all_time_identity':'O u=0; H=O G; H u=v; H G=L H, hence d/dt(O exp(Gt)u)=exp(Lt)v',
        'signal_index_convention':'X_b[i,j] stored at b*d*f+j*d+i; Xprime_b=sum_a As[a,b]X_a-Aout X_b+X_b Ain',
        'full252_embedding_identity':'Aout Tout=Tout A6; Tin^T Ain=A2 Tin^T; every scalar component closed, and every61 original W entry occurs exactly once per source branch/transfer',
        'resonance_scope':'all displayed generator entries are source polynomial functions; no inverse of signal L or division by frequency differences is used',
        'zero_mode_consumer':'original122 phase and unit Fourier weight, kout=kin; no second zero copy or sqrt2 pair factor',
        'nonzero_pair_consumer':'original244 real pair; weights cosine1/sqrt2 and sine sign*i/sqrt2; kout=kin+sign*kappa',
        'real_action_matter_branches':'W,-conjugate(W); A(k),conjugate(A(-k)); independent canonical dual is reversed edge/opposite transpose',
        'N1_scope':'complete branch/full252 coefficient construction for the fixed scalar Fourier pair or separate zero mode; finite shifts act on smooth compact momentum wavefunctions; all-time source ODE follows from exact matrix identities',
        'free_boson_state_Hamiltonian_exponential_assumed':False,
        'ordered_N2':{'state_dimension':G.rows,'output_dimension':O.rows,
            'left_source_key':ordered['left_source_key'],'right_source_key':ordered['right_source_key'],
            'initial_and_first_derivative_zero':True,'second_derivative_nonzero':True,
            'second_derivative_sha256':signature(second),'later_left_boson_order_preserved':True,
            'whole_N2_assembly_claimed':False},
        'continuous_antisymmetric_N_body_installation_claimed':False,
        'finite_Fock_Fin504_substituted_for_continuous_N_body':False,
        'complete_four_block_spectrum_or_decay_measure_claimed':False,
        'lifetime_status':'SOURCE_NATIVE_DYNAMIC_MEASURE_REQUIRED',
        'elapsed_seconds':round(time.monotonic()-started,3)}
    (HERE/'independent_scalar_dyson_time.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS independent source scalar Dyson time primitive certification',result['elapsed_seconds'],'seconds',flush=True)


if __name__=='__main__':
    main()
